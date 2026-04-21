#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
#
# extract_typechecker_ecosystem.jl
#
# Expands ECHIDNA's corpus with typechecker-heavy proof obligations drawn from:
#   - verification-ecosystem/typell
#   - developer-ecosystem/katagoria
#   - verification-ecosystem/tropical-resource-typing
#
# Focus: broaden prover/tool diversity and add deep support vocabulary for
# choreographic, epistemic, tropical, echo, modal, session, QTT, and dependent
# type checking.
#
# Output:
#   training_data/proof_states_typechecker_ecosystem.jsonl
#   training_data/stats_typechecker_ecosystem.json

using Dates
using JSON3

const REPO_ROOT = dirname(dirname(abspath(@__FILE__)))
const TRAINING_DIR = joinpath(REPO_ROOT, "training_data")
const OUTPUT_FILE = joinpath(TRAINING_DIR, "proof_states_typechecker_ecosystem.jsonl")
const PREMISES_FILE = joinpath(TRAINING_DIR, "premises_typechecker_ecosystem.jsonl")
const STATS_FILE = joinpath(TRAINING_DIR, "stats_typechecker_ecosystem.json")
const START_ID = 320000
const TARGET_PER_TOOL = 220

const TYPELL_ROOT = abspath(joinpath(REPO_ROOT, "..", "typell"))
const KATAGORIA_ROOT = abspath(joinpath(REPO_ROOT, "..", "..", "developer-ecosystem", "katagoria"))
const TROPICAL_ROOT = abspath(joinpath(REPO_ROOT, "..", "tropical-resource-typing"))

const TOOL_ORDER = [
    "TypeLL",
    "KatagoriaVerifier",
    "TropicalTypeChecker",
    "ChoreographicTypeChecker",
    "EpistemicTypeChecker",
    "EchoTypeChecker",
    "SessionTypeChecker",
    "ModalTypeChecker",
    "QTTTypeChecker",
    "EffectRowTypeChecker",
    "DependentTypeChecker",
    "RefinementTypeChecker",
]

const TOOL_KEYWORDS = Dict(
    "TypeLL" => Set([
        "typell", "kernel", "discipline", "unification", "inference", "checker",
        "obligation", "proof", "judgement", "typing", "typechecker",
    ]),
    "KatagoriaVerifier" => Set([
        "katagoria", "verification", "traceability", "safety", "proof", "abi",
        "contract", "integrity", "template", "governance",
    ]),
    "TropicalTypeChecker" => Set([
        "tropical", "semiring", "kleene", "matrix", "dioid", "walk", "path",
        "resource", "latency", "throughput", "min-plus", "max-plus",
    ]),
    "ChoreographicTypeChecker" => Set([
        "choreographic", "choreography", "endpoint", "global", "projection",
        "session", "protocol", "channel", "duality", "multiparty",
    ]),
    "EpistemicTypeChecker" => Set([
        "epistemic", "knowledge", "belief", "agent", "accessible", "accessibility",
        "security", "information", "flow", "noninterference",
    ]),
    "EchoTypeChecker" => Set([
        "echo", "reflection", "feedback", "trace", "replay", "echoed",
        "idempotent", "self-check", "witness", "stability",
    ]),
    "SessionTypeChecker" => Set([
        "session", "send", "recv", "offer", "select", "endpoint", "dual",
        "protocol", "channel", "recursion",
    ]),
    "ModalTypeChecker" => Set([
        "modal", "box", "dia", "context", "phase", "transaction", "necessity",
        "possibility", "scope", "mode",
    ]),
    "QTTTypeChecker" => Set([
        "qtt", "quantitative", "quantifier", "usage", "linear", "affine",
        "omega", "bounded", "semiring", "consumption",
    ]),
    "EffectRowTypeChecker" => Set([
        "effect", "effects", "row", "handler", "io", "state", "except",
        "network", "filesystem", "subrow",
    ]),
    "DependentTypeChecker" => Set([
        "dependent", "sigma", "pi", "index", "term", "equality", "recursor",
        "inductive", "coinductive", "universe",
    ]),
    "RefinementTypeChecker" => Set([
        "refinement", "predicate", "constraint", "smt", "invariant", "safety",
        "proof-carrying", "subtype", "validity", "witness",
    ]),
)

const SYNTH_LEXICON = Dict(
    "TypeLL" => ["unification", "bidirectional", "discipline", "proof-obligation", "normalization"],
    "KatagoriaVerifier" => ["traceability", "compliance", "contract", "invariant", "safety-case"],
    "TropicalTypeChecker" => ["tropical", "semiring", "kleene", "path-weight", "resource-budget"],
    "ChoreographicTypeChecker" => ["choreography", "projection", "endpoint", "session", "global-type"],
    "EpistemicTypeChecker" => ["epistemic", "knowledge", "accessibility", "belief", "noninterference"],
    "EchoTypeChecker" => ["echo", "feedback", "reflection", "trace", "stability"],
    "SessionTypeChecker" => ["duality", "offer", "select", "recv", "send"],
    "ModalTypeChecker" => ["modal", "box", "dia", "phase", "context"],
    "QTTTypeChecker" => ["quantifier", "usage", "linear", "affine", "omega"],
    "EffectRowTypeChecker" => ["effect-row", "handler", "subrow", "declared", "discovered"],
    "DependentTypeChecker" => ["dependent", "index", "sigma", "pi", "transport"],
    "RefinementTypeChecker" => ["refinement", "predicate", "constraint", "solver", "proof-carrying"],
)

const SIGNAL_RE = r"(theorem|lemma|corollary|proposition|typing|type|session|choreograph|epistemic|modal|effect|invariant|requires|ensures|decreases|instance|proof|rule|semiring|kleene|resource|unification|quantifier)"i

const TYPELL_FILES = [
    "spec/type-system/dependent.adoc",
    "spec/type-system/linear.adoc",
    "spec/type-system/session.adoc",
    "spec/type-system/modal.adoc",
    "spec/type-system/effects.adoc",
    "spec/type-system/qtt.adoc",
    "spec/proof/proof-system.adoc",
    "spec/protocol/TYPELL-PROTOCOL.adoc",
    "crates/typell-core/src/types.rs",
    "crates/typell-core/src/session.rs",
    "crates/typell-core/src/effects.rs",
    "crates/typell-core/src/qtt.rs",
    "crates/typell-eclexia/src/lib.rs",
]

const KATAGORIA_FILES = [
    "verification/proofs/idris2/Types.idr",
    "verification/proofs/lean4/ApiTypes.lean",
    "verification/proofs/coq/TypeSafety.v",
    "verification/proofs/agda/Properties.agda",
    "verification/proofs/tlaplus/StateMachine.tla",
    "research/tropical/TropicalKleene.idr",
    "research/tropical/README.adoc",
    "verification/proofs/README.adoc",
]

const TROPICAL_FILES = [
    "Tropical_v2.thy",
    "Tropical_Matrices_Full.thy",
    "Tropical_Kleene.thy",
    "Tropical_CNO.thy",
    "Tropical_Determinants.thy",
    "TropicalSessionTypes.lean",
    "docs/FORMAL-PROOFS.adoc",
]

mutable struct Entry
    prover::String
    theorem::String
    goal::String
    context::Vector{String}
    tactic_proof::String
    source::String
    synthetic::Bool
end

function clean_text(s::AbstractString, max_len::Int)::String
    compact = replace(strip(String(s)), r"\s+" => " ")
    return first(compact, max_len)
end

function tokenize(s::String)::Vector{String}
    [lowercase(m.match) for m in eachmatch(r"[A-Za-z][A-Za-z0-9_+-]*", s)]
end

function extract_context(snippet::String, prover::String)::Vector{String}
    tokens = tokenize(snippet)
    freq = Dict{String,Int}()
    for t in tokens
        length(t) < 4 && continue
        freq[t] = get(freq, t, 0) + 1
    end
    sorted = sort(collect(keys(freq)); by=t -> (-freq[t], t))
    base = sorted[1:min(10, length(sorted))]
    kws = collect(TOOL_KEYWORDS[prover])
    matched = [k for k in kws if occursin(k, lowercase(snippet))]
    append!(base, matched[1:min(4, length(matched))])
    return unique(base)
end

function fallback_tool(path::String)::String
    low = lowercase(path)
    if occursin("tropical", low)
        return "TropicalTypeChecker"
    elseif occursin("session", low) || occursin("tlaplus", low) || endswith(low, ".tla")
        return "ChoreographicTypeChecker"
    elseif occursin("modal", low) || occursin("security", low)
        return "EpistemicTypeChecker"
    elseif occursin("effect", low)
        return "EffectRowTypeChecker"
    elseif occursin("qtt", low) || occursin("linear", low)
        return "QTTTypeChecker"
    elseif occursin("dependent", low)
        return "DependentTypeChecker"
    elseif occursin("katagoria", low)
        return "KatagoriaVerifier"
    else
        return "TypeLL"
    end
end

function classify_tool(path::String, snippet::String)::String
    toks = Set(tokenize(snippet))
    best_tool = fallback_tool(path)
    best_score = -1
    for tool in TOOL_ORDER
        score = count(k -> k in toks || occursin(k, lowercase(snippet)), TOOL_KEYWORDS[tool])
        if score > best_score
            best_score = score
            best_tool = tool
        elseif score == best_score && score > 0
            # Keep stable ordering when tied.
            if findfirst(==(tool), TOOL_ORDER) < findfirst(==(best_tool), TOOL_ORDER)
                best_tool = tool
            end
        end
    end
    return best_score <= 0 ? fallback_tool(path) : best_tool
end

function gather_candidates(lines::Vector{String})::Vector{Tuple{Int,String}}
    out = Tuple{Int,String}[]
    for i in eachindex(lines)
        line = strip(lines[i])
        isempty(line) && continue
        if !occursin(SIGNAL_RE, line)
            continue
        end
        if startswith(line, "//") || startswith(line, "--") || startswith(line, "# ")
            continue
        end
        snippet = line
        if i < length(lines)
            nxt = strip(lines[i + 1])
            if !isempty(nxt) && !startswith(nxt, "//") && !startswith(nxt, "--")
                snippet = string(snippet, " ", nxt)
            end
        end
        length(snippet) < 24 && continue
        push!(out, (i, clean_text(snippet, 420)))
    end
    return out
end

function read_sources()::Vector{Tuple{String,String}}
    files = Tuple{String,String}[]
    for rel in TYPELL_FILES
        path = joinpath(TYPELL_ROOT, rel)
        isfile(path) || continue
        push!(files, (path, "typell/$rel"))
    end
    for rel in KATAGORIA_FILES
        path = joinpath(KATAGORIA_ROOT, rel)
        isfile(path) || continue
        push!(files, (path, "katagoria/$rel"))
    end
    for rel in TROPICAL_FILES
        path = joinpath(TROPICAL_ROOT, rel)
        isfile(path) || continue
        push!(files, (path, "tropical-resource-typing/$rel"))
    end
    return files
end

function theorem_slug(source_rel::String, line_no::Int)::String
    base = replace(basename(source_rel), r"\.[^.]+$" => "")
    clean = replace(lowercase(base), r"[^a-z0-9]+" => "_")
    return "$(clean)_line_$(line_no)"
end

function synth_goal(tool::String, a::String, b::String, c::String)::String
    templates = [
        "Prove $a is preserved by $b under $c typing constraints.",
        "Show $b remains sound when composed with $c in the $a fragment.",
        "Establish $c completeness for $a-driven $b derivations.",
        "Check $a and $b are compatible with $c in bidirectional checking.",
        "Derive a progress and preservation condition linking $a, $b, and $c.",
    ]
    idx = mod(length(a) + length(b) + length(c), length(templates)) + 1
    return templates[idx]
end

function synth_tactic(tool::String, a::String, b::String, c::String)::String
    if tool == "TropicalTypeChecker"
        return "normalize; apply semiring laws; discharge tropical obligations;"
    elseif tool == "ChoreographicTypeChecker" || tool == "SessionTypeChecker"
        return "project endpoints; check duality; close protocol obligations;"
    elseif tool == "EpistemicTypeChecker" || tool == "ModalTypeChecker"
        return "lift context; apply accessibility rule; prove modal compatibility;"
    else
        return "infer constraints; normalize terms; discharge proof obligations;"
    end
end

function generate_entries()::Tuple{Vector{Entry},Int,Int,Vector{String}}
    entries = Entry[]
    seen = Set{Tuple{String,String}}()
    source_refs = String[]

    extracted = 0
    synthetic = 0

    for (path, source_rel) in read_sources()
        push!(source_refs, source_rel)
        lines = readlines(path)
        for (line_no, snippet) in gather_candidates(lines)
            tool = classify_tool(source_rel, snippet)
            theorem = theorem_slug(source_rel, line_no)
            key = (tool, snippet)
            key in seen && continue
            push!(seen, key)
            push!(entries, Entry(
                tool,
                theorem,
                snippet,
                extract_context(snippet, tool),
                "source:$source_rel line:$line_no",
                "typechecker_ecosystem/$source_rel",
                false,
            ))
            extracted += 1
        end
    end

    # Balance each tool with synthetic obligations to reduce skew.
    counts = Dict(tool => 0 for tool in TOOL_ORDER)
    for e in entries
        counts[e.prover] = get(counts, e.prover, 0) + 1
    end

    for tool in TOOL_ORDER
        missing = max(0, TARGET_PER_TOOL - get(counts, tool, 0))
        lex = SYNTH_LEXICON[tool]
        for i in 1:missing
            a = lex[mod(i - 1, length(lex)) + 1]
            b = lex[mod(i + 1, length(lex)) + 1]
            c = lex[mod(i + 3, length(lex)) + 1]
            goal = synth_goal(tool, a, b, c)
            theorem = "$(lowercase(replace(tool, r"[^A-Za-z0-9]+" => "_")))_synth_$(lpad(string(i), 4, '0'))"
            key = (tool, goal)
            key in seen && continue
            push!(seen, key)
            push!(entries, Entry(
                tool,
                theorem,
                goal,
                unique([a, b, c, "typing", "soundness", "obligation"]),
                synth_tactic(tool, a, b, c),
                "typechecker_ecosystem/synthetic/$tool",
                true,
            ))
            synthetic += 1
        end
    end

    return entries, extracted, synthetic, sort(unique(source_refs))
end

function write_output(entries::Vector{Entry})::Dict{String,Int}
    sort!(entries, by=e -> (e.prover, e.theorem))
    prover_counts = Dict{String,Int}()

    mkpath(TRAINING_DIR)
    premises_records = Dict{String,Any}[]
    open(OUTPUT_FILE, "w") do fh
        for (idx, e) in enumerate(entries)
            record_id = START_ID + idx - 1
            record = Dict{String,Any}(
                "id" => record_id,
                "prover" => e.prover,
                "theorem" => e.theorem,
                "goal" => e.goal,
                "context" => e.context,
                "tactic_proof" => e.tactic_proof,
                "source" => e.source,
            )
            println(fh, JSON3.write(record))
            # Emit premises: identifiers from typechecker goal snippet
            for hm in eachmatch(r"\b([a-zA-Z][a-zA-Z0-9_\-]{1,40})\b", e.goal)
                h = strip(hm.captures[1])
                !isempty(h) && length(h) < 50 && push!(premises_records, Dict{String,Any}(
                    "proof_id"=>record_id, "premise"=>h,
                    "prover"=>e.prover, "theorem"=>e.theorem, "source"=>"typechecker_ecosystem"))
            end
            prover_counts[e.prover] = get(prover_counts, e.prover, 0) + 1
        end
    end
    open(PREMISES_FILE, "w") do fh
        for p in premises_records; println(fh, JSON3.write(p)); end
    end
    return prover_counts
end

function run()::Int
    println("[typechecker-ecosystem] extracting corpus entries ...")
    entries, extracted, synthetic, source_refs = generate_entries()
    prover_counts = write_output(entries)

    stats = Dict{String,Any}(
        "version" => "v2.2-typechecker-ecosystem",
        "date" => string(today()),
        "output_file" => OUTPUT_FILE,
        "total_entries" => length(entries),
        "extracted_entries" => extracted,
        "synthetic_entries" => synthetic,
        "target_per_tool" => TARGET_PER_TOOL,
        "tool_counts" => Dict(k => get(prover_counts, k, 0) for k in TOOL_ORDER),
        "source_files" => source_refs,
    )

    open(STATS_FILE, "w") do fh
        JSON3.pretty(fh, stats)
    end

    println("[typechecker-ecosystem] wrote $(length(entries)) entries to $OUTPUT_FILE")
    println("[typechecker-ecosystem] wrote stats to $STATS_FILE")
    return length(entries)
end

if abspath(PROGRAM_FILE) == @__FILE__
    run()
end
