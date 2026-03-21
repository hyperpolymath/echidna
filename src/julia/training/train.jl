# SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
# SPDX-License-Identifier: PMPL-1.0-or-later

"""
    training/train.jl

Training Pipeline for ECHIDNA Neural Solver

Implements training loop, data loading, loss functions, and optimization
for the universal neural premise selector across all 12 theorem provers.

Features:
- Multi-prover training with balanced sampling
- Contrastive learning for premise ranking
- Learning rate scheduling
- Early stopping and checkpointing
- Distributed training support (multi-GPU)
- Metrics tracking and logging
"""

using Flux
using Optimisers
using CUDA
using Statistics
using Random
using Logging
using JSON3
using BSON
using Dates
using ProgressMeter

# ============================================================================
# Data Structures
# ============================================================================

"""
    TrainingExample

Single training example with proof state, relevant premises, and labels.
"""
struct TrainingExample
    proof_state::ProofState
    candidate_premises::Vector{Premise}
    relevant_indices::Vector{Int}  # Indices of actually useful premises
    prover::ProverType
end

"""
    TrainingDataset

Collection of training examples with batching support.
"""
mutable struct TrainingDataset
    examples::Vector{TrainingExample}
    batch_size::Int
    shuffle::Bool
    current_idx::Int
end

function TrainingDataset(examples::Vector{TrainingExample}; batch_size::Int=32, shuffle::Bool=true)
    return TrainingDataset(examples, batch_size, shuffle, 1)
end

"""
    next_batch!(dataset::TrainingDataset)

Get next batch of training examples. Returns nothing when epoch is complete.
"""
function next_batch!(dataset::TrainingDataset)
    if dataset.current_idx > length(dataset.examples)
        # Epoch complete - shuffle and reset
        if dataset.shuffle
            shuffle!(dataset.examples)
        end
        dataset.current_idx = 1
        return nothing
    end

    # Get batch
    end_idx = min(dataset.current_idx + dataset.batch_size - 1, length(dataset.examples))
    batch = dataset.examples[dataset.current_idx:end_idx]
    dataset.current_idx = end_idx + 1

    return batch
end

"""
    reset!(dataset::TrainingDataset)

Reset dataset to beginning.
"""
function reset!(dataset::TrainingDataset)
    dataset.current_idx = 1
    if dataset.shuffle
        shuffle!(dataset.examples)
    end
end

# ============================================================================
# Loss Functions
# ============================================================================

"""
    ranking_loss(scores::Vector{Float32}, relevant_indices::Vector{Int})

Binary cross-entropy loss for premise selection (Zygote-differentiable).
Uses a label vector: 1 for relevant, 0 for irrelevant.
"""
function ranking_loss(scores::Vector{Float32}, relevant_indices::Vector{Int})
    n = length(scores)
    if n == 0 || isempty(relevant_indices)
        return 0.0f0
    end

    # Build label vector (outside gradient graph)
    labels = Zygote.@ignore begin
        rel_set = Set(relevant_indices)
        Float32[i in rel_set ? 1.0f0 : 0.0f0 for i in 1:n]
    end

    # Binary cross-entropy loss
    eps = 1f-7
    clamped = clamp.(scores, eps, 1.0f0 - eps)
    loss = -mean(labels .* log.(clamped) .+ (1.0f0 .- labels) .* log.(1.0f0 .- clamped))

    return loss
end

"""
    contrastive_loss(scores::Vector{Float32}, relevant_indices::Vector{Int}; temperature::Float32=0.1f0)

InfoNCE contrastive loss for premise selection (Zygote-differentiable).
"""
function contrastive_loss(scores::Vector{Float32}, relevant_indices::Vector{Int}; temperature::Float32=0.1f0)
    if isempty(relevant_indices) || length(scores) == 0
        return 0.0f0
    end

    # Normalize scores with temperature
    scaled_scores = scores ./ temperature
    log_sum_exp = log(sum(exp.(scaled_scores)) + 1f-10)

    # InfoNCE: -log(exp(s_pos) / sum(exp(s_all))) for each positive
    loss = 0.0f0
    for rel_idx in relevant_indices
        loss += log_sum_exp - scaled_scores[rel_idx]
    end

    return loss / Float32(length(relevant_indices))
end

"""
    pre_encode_batch(solver::NeuralSolver, batch::Vector{TrainingExample})

Pre-encode a batch of examples into token ID matrices (non-differentiable step).
Returns vector of (goal_ids, premise_ids_list, relevant_indices) tuples.
"""
function pre_encode_batch(solver::NeuralSolver, batch::Vector{TrainingExample})
    encoded = []
    vocab = solver.vocabulary
    unk_id = vocab.token_to_id[vocab.unk_token]
    sep_id = vocab.token_to_id[vocab.sep_token]

    for example in batch
        # Tokenize and encode goal
        goal_tokens = tokenize_text(example.proof_state.goal)
        goal_ids = encode_tokens(vocab, goal_tokens)

        # Ensure minimum length
        if isempty(goal_ids)
            goal_ids = [unk_id]
        end

        # Build token matrix for goal (seq_len, 1)
        goal_matrix = reshape(goal_ids, length(goal_ids), 1)

        # Pre-encode each premise
        premise_matrices = []
        for prem in example.candidate_premises
            prem_tokens = tokenize_text(prem.name * " " * prem.statement)
            prem_ids = encode_tokens(vocab, prem_tokens)
            if isempty(prem_ids)
                prem_ids = [unk_id]
            end
            push!(premise_matrices, reshape(prem_ids, length(prem_ids), 1))
        end

        push!(encoded, (goal_matrix, premise_matrices, example.relevant_indices))
    end

    return encoded
end

"""
    combined_loss(solver::NeuralSolver, batch::Vector{TrainingExample}; α::Float32=0.5f0)

Combined loss function: ranking + contrastive learning.
Pre-encodes tokens (non-differentiable), then runs neural forward pass (differentiable).
"""
function combined_loss(solver::NeuralSolver, batch::Vector{TrainingExample}; α::Float32=0.5f0)
    total_loss = 0.0f0
    batch_size = length(batch)

    # Pre-encode outside gradient (dict lookups are not differentiable)
    encoded_batch = pre_encode_batch(solver, batch)

    for (goal_matrix, premise_matrices, relevant_indices) in encoded_batch
        # Neural forward pass (differentiable)
        goal_embed = solver.text_encoder(goal_matrix)  # (embed_dim, seq_len, 1)
        goal_vec = mean(goal_embed, dims=2)[:, 1, 1]   # (embed_dim,)

        # Encode each premise
        num_premises = length(premise_matrices)
        embed_dim = length(goal_vec)
        premise_vecs = zeros(Float32, embed_dim, num_premises)

        for (i, pmat) in enumerate(premise_matrices)
            prem_embed = solver.text_encoder(pmat)
            premise_vecs[:, i] = mean(prem_embed, dims=2)[:, 1, 1]
        end

        # Score premises by cosine similarity with goal
        goal_norm = goal_vec ./ (sqrt(sum(goal_vec .^ 2)) + 1f-10)
        prem_norms = premise_vecs ./ (sqrt.(sum(premise_vecs .^ 2, dims=1)) .+ 1f-10)
        scores = vec(goal_norm' * prem_norms)  # (num_premises,)

        # Compute losses
        rank_loss = ranking_loss(scores, relevant_indices)
        contrast_loss = contrastive_loss(scores, relevant_indices)

        total_loss += α * rank_loss + (1 - α) * contrast_loss
    end

    return total_loss / batch_size
end

# ============================================================================
# Metrics
# ============================================================================

"""
    TrainingMetrics

Track training metrics over time.
"""
mutable struct TrainingMetrics
    epoch::Vector{Int}
    train_loss::Vector{Float32}
    val_loss::Vector{Float32}
    precision_at_k::Vector{Float32}  # Precision@10
    recall_at_k::Vector{Float32}     # Recall@10
    mrr::Vector{Float32}              # Mean Reciprocal Rank
    learning_rate::Vector{Float32}
    timestamp::Vector{DateTime}
end

function TrainingMetrics()
    return TrainingMetrics(
        Int[], Float32[], Float32[], Float32[], Float32[], Float32[], Float32[], DateTime[]
    )
end

"""
    compute_metrics(solver::NeuralSolver, dataset::TrainingDataset; k::Int=10)

Compute evaluation metrics on a dataset.
"""
function compute_metrics(solver::NeuralSolver, dataset::TrainingDataset; k::Int=10)
    reset!(dataset)

    total_precision = 0.0f0
    total_recall = 0.0f0
    total_mrr = 0.0f0
    num_examples = 0

    Flux.testmode!(solver)

    while true
        batch = next_batch!(dataset)
        batch === nothing && break

        # Pre-encode batch (same approach as training)
        encoded_batch = pre_encode_batch(solver, batch)

        for (i, (goal_matrix, premise_matrices, relevant_indices)) in enumerate(encoded_batch)
            # Score via cosine similarity (same as training loss)
            goal_embed = solver.text_encoder(goal_matrix)
            goal_vec = mean(goal_embed, dims=2)[:, 1, 1]
            prem_vecs = [mean(solver.text_encoder(pmat), dims=2)[:, 1, 1] for pmat in premise_matrices]
            premise_vecs = hcat(prem_vecs...)

            goal_norm = goal_vec ./ (sqrt(sum(goal_vec .^ 2)) + 1f-10)
            prem_norms = premise_vecs ./ (sqrt.(sum(premise_vecs .^ 2, dims=1)) .+ 1f-10)
            scores = vec(goal_norm' * prem_norms)

            # Get top-k predictions
            actual_k = min(k, length(scores))
            top_k_indices = partialsortperm(scores, 1:actual_k, rev=true)

            # Precision@k
            num_relevant_in_top_k = length(intersect(top_k_indices, relevant_indices))
            precision = num_relevant_in_top_k / actual_k

            # Recall@k
            recall = num_relevant_in_top_k / max(1, length(relevant_indices))

            # MRR
            mrr = 0.0f0
            for (rank, idx) in enumerate(top_k_indices)
                if idx in relevant_indices
                    mrr = 1.0f0 / rank
                    break
                end
            end

            total_precision += precision
            total_recall += recall
            total_mrr += mrr
            num_examples += 1
        end
    end

    Flux.trainmode!(solver)

    num_examples = max(num_examples, 1)
    return (
        precision = total_precision / num_examples,
        recall = total_recall / num_examples,
        mrr = total_mrr / num_examples
    )
end

"""
    log_metrics!(metrics::TrainingMetrics, epoch::Int, train_loss::Float32,
                 val_loss::Float32, val_metrics, lr::Float32)

Log metrics for current epoch.
"""
function log_metrics!(metrics::TrainingMetrics, epoch::Int, train_loss::Float32,
                      val_loss::Float32, val_metrics, lr::Float32)
    push!(metrics.epoch, epoch)
    push!(metrics.train_loss, train_loss)
    push!(metrics.val_loss, val_loss)
    push!(metrics.precision_at_k, val_metrics.precision)
    push!(metrics.recall_at_k, val_metrics.recall)
    push!(metrics.mrr, val_metrics.mrr)
    push!(metrics.learning_rate, lr)
    push!(metrics.timestamp, now())

    @info "Epoch $epoch" train_loss val_loss precision=val_metrics.precision recall=val_metrics.recall mrr=val_metrics.mrr lr
end

"""
    save_metrics(metrics::TrainingMetrics, path::String)

Save metrics to JSONL file.
"""
function save_metrics(metrics::TrainingMetrics, path::String)
    open(path, "w") do io
        for i in eachindex(metrics.epoch)
            entry = Dict{String, Any}(
                "epoch" => metrics.epoch[i],
                "train_loss" => metrics.train_loss[i],
                "learning_rate" => metrics.learning_rate[i],
                "timestamp" => string(metrics.timestamp[i])
            )
            if i <= length(metrics.val_loss)
                entry["val_loss"] = metrics.val_loss[i]
                entry["precision_at_10"] = metrics.precision_at_k[i]
                entry["recall_at_10"] = metrics.recall_at_k[i]
                entry["mrr"] = metrics.mrr[i]
            end
            println(io, JSON3.write(entry))
        end
    end
    @info "Metrics saved to $path"
end

# ============================================================================
# Training Loop
# ============================================================================

"""
    TrainingConfig

Configuration for training process.
"""
mutable struct TrainingConfig
    num_epochs::Int
    learning_rate::Float32
    lr_schedule::Symbol  # :constant, :exponential, :cosine
    lr_decay_rate::Float32
    weight_decay::Float32
    gradient_clip_norm::Float32
    loss_alpha::Float32  # Weight for ranking vs contrastive loss
    early_stopping_patience::Int
    checkpoint_every::Int
    eval_every::Int
    save_dir::String
end

function TrainingConfig(;
    num_epochs::Int=100,
    learning_rate::Float32=1f-4,
    lr_schedule::Symbol=:cosine,
    lr_decay_rate::Float32=0.95f0,
    weight_decay::Float32=1f-5,
    gradient_clip_norm::Float32=1.0f0,
    loss_alpha::Float32=0.5f0,
    early_stopping_patience::Int=10,
    checkpoint_every::Int=5,
    eval_every::Int=1,
    save_dir::String="checkpoints"
)
    return TrainingConfig(
        num_epochs, learning_rate, lr_schedule, lr_decay_rate, weight_decay,
        gradient_clip_norm, loss_alpha, early_stopping_patience,
        checkpoint_every, eval_every, save_dir
    )
end

"""
    get_learning_rate(config::TrainingConfig, epoch::Int)

Compute learning rate for current epoch based on schedule.
"""
function get_learning_rate(config::TrainingConfig, epoch::Int)
    base_lr = config.learning_rate

    if config.lr_schedule == :constant
        return base_lr
    elseif config.lr_schedule == :exponential
        return Float32(base_lr * (config.lr_decay_rate ^ (epoch - 1)))
    elseif config.lr_schedule == :cosine
        # Cosine annealing
        return Float32(base_lr * 0.5f0 * (1.0f0 + cos(Float32(π) * epoch / config.num_epochs)))
    else
        @warn "Unknown learning rate schedule: $(config.lr_schedule), using constant"
        return base_lr
    end
end

"""
    train_solver!(solver::NeuralSolver, train_data::TrainingDataset,
                  val_data::TrainingDataset; config::TrainingConfig=TrainingConfig())

Train the neural solver on provided data.
"""
function train_solver!(solver::NeuralSolver, train_data::TrainingDataset,
                       val_data::TrainingDataset; config::TrainingConfig=TrainingConfig())
    @info "Starting training with config" config

    # Create save directory
    mkpath(config.save_dir)

    # Initialize optimizer with gradient clipping
    opt_rule = Optimisers.OptimiserChain(
        Optimisers.ClipNorm(config.gradient_clip_norm),
        Optimisers.Adam(config.learning_rate)
    )
    opt_state = Flux.setup(opt_rule, solver)

    # Metrics tracking
    metrics = TrainingMetrics()
    best_val_loss = Inf32
    patience_counter = 0

    # Training loop
    for epoch in 1:config.num_epochs
        @info "Epoch $epoch / $(config.num_epochs)"

        # Update learning rate
        current_lr = get_learning_rate(config, epoch)
        Optimisers.adjust!(opt_state, Float32(current_lr))

        # Training epoch
        reset!(train_data)
        epoch_loss = 0.0f0
        num_batches = 0

        progress = Progress(ceil(Int, length(train_data.examples) / train_data.batch_size),
                           desc="Training: ")

        while true
            batch = next_batch!(train_data)
            batch === nothing && break

            # Pre-encode tokens (non-differentiable)
            encoded_batch = pre_encode_batch(solver, batch)

            # Compute loss and gradients (only neural forward pass is differentiable)
            loss, grads = Flux.withgradient(solver) do m
                _loss = 0.0f0
                for (goal_matrix, premise_matrices, relevant_indices) in encoded_batch
                    goal_embed = m.text_encoder(goal_matrix)
                    goal_vec = mean(goal_embed, dims=2)[:, 1, 1]

                    # Encode premises without mutation (hcat instead of setindex!)
                    prem_vecs = [mean(m.text_encoder(pmat), dims=2)[:, 1, 1] for pmat in premise_matrices]
                    premise_vecs = hcat(prem_vecs...)  # (embed_dim, num_premises)

                    # Cosine similarity scores
                    goal_norm = goal_vec ./ (sqrt(sum(goal_vec .^ 2)) + 1f-10)
                    prem_norms = premise_vecs ./ (sqrt.(sum(premise_vecs .^ 2, dims=1)) .+ 1f-10)
                    scores = vec(goal_norm' * prem_norms)

                    _loss += config.loss_alpha * ranking_loss(scores, relevant_indices) +
                             (1 - config.loss_alpha) * contrastive_loss(scores, relevant_indices)
                end
                _loss / length(encoded_batch)
            end

            # Update parameters (gradient clipping via Optimisers.ClipNorm in opt setup)
            Flux.update!(opt_state, solver, grads[1])

            epoch_loss += loss
            num_batches += 1

            next!(progress, showvalues=[(:loss, loss)])
        end

        avg_train_loss = epoch_loss / num_batches

        # Validation
        if epoch % config.eval_every == 0
            @info "Running validation..."

            # Compute validation loss
            reset!(val_data)
            val_loss = 0.0f0
            val_batches = 0

            Flux.testmode!(solver)  # Disable dropout
            while true
                batch = next_batch!(val_data)
                batch === nothing && break

                loss = combined_loss(solver, batch, α=config.loss_alpha)
                val_loss += loss
                val_batches += 1
            end
            Flux.trainmode!(solver)  # Re-enable dropout

            avg_val_loss = val_loss / val_batches

            # Compute metrics
            val_metrics = compute_metrics(solver, val_data)

            # Log metrics
            log_metrics!(metrics, epoch, avg_train_loss, avg_val_loss, val_metrics, current_lr)

            # Early stopping check
            if avg_val_loss < best_val_loss
                best_val_loss = avg_val_loss
                patience_counter = 0

                # Save best model
                save_solver(solver, joinpath(config.save_dir, "best_model"))
            else
                patience_counter += 1
                if patience_counter >= config.early_stopping_patience
                    @info "Early stopping triggered after $epoch epochs"
                    break
                end
            end
        else
            # Just log training loss
            push!(metrics.epoch, epoch)
            push!(metrics.train_loss, avg_train_loss)
            push!(metrics.learning_rate, current_lr)
            push!(metrics.timestamp, now())
        end

        # Checkpoint
        if epoch % config.checkpoint_every == 0
            checkpoint_path = joinpath(config.save_dir, "checkpoint_epoch_$epoch")
            save_solver(solver, checkpoint_path)
        end
    end

    # Save final metrics
    save_metrics(metrics, joinpath(config.save_dir, "training_metrics.csv"))

    @info "Training complete!"
    return metrics
end

# ============================================================================
# Data Loading Utilities
# ============================================================================

# NOTE: load_training_data is defined in training/dataloader.jl (included before this file).
# It reads JSONL files and returns (train_data, val_data, vocab).

export TrainingExample, TrainingDataset, next_batch!, reset!
export ranking_loss, contrastive_loss, combined_loss
export TrainingMetrics, compute_metrics, log_metrics!, save_metrics
export TrainingConfig, train_solver!
