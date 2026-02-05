# SPDX-License-Identifier: PMPL-1.0-or-later
# Enhanced proof extraction for all 12 provers

using Dates

const PROOFS_DIR = "proofs"
const OUTPUT_DIR = "training_data"

# Simple proof extraction patterns for each prover
PATTERNS = Dict(
    # Coq/Rocq
    "coq" => (
        ext=[".v"],
        theorem=r"(?:Theorem|Lemma|Corollary)\s+(\w+)\s*:",
        tactic=r"^\s*(\w+)\.?\s*$",
        goal=r":\s*(.+)\."
    ),

    # Lean
    "lean" => (
        ext=[".lean"],
        theorem=r"theorem\s+(\w+)",
        tactic=r"^\s*(\w+)\s",
        goal=r":\s*(.+):="
    ),

    # Isabelle
    "isabelle" => (
        ext=[".thy"],
        theorem=r"theorem\s+(\w+)",
        tactic=r"^\s*(?:by|apply)\s+(\w+)",
        goal=r"shows\s+\"(.+)\""
    ),

    # Agda
    "agda" => (
        ext=[".agda"],
        theorem=r"(\w+)\s*:",
        tactic=r"rewrite",
        goal=r":\s*(.+)"
    ),

    # ACL2
    "acl2" => (
        ext=[".lisp"],
        theorem=r"\(defthm\s+(\w+)",
        tactic=r":hints",
        goal=r"\(defthm\s+\w+\s+(.+?)\)"
    ),

    # PVS
    "pvs" => (
        ext=[".pvs"],
        theorem=r"(\w+)\s*:",
        tactic=r"FORMULA|LEMMA",
        goal=r":\s*(.+)"
    ),

    # HOL4
    "hol4" => (
        ext=[".sml"],
        theorem=r"Theorem\s+(\w+)",
        tactic=r"(?:rw|simp|metis_tac)",
        goal=r"'(.+)'"
    ),

    # Mizar
    "mizar" => (
        ext=[".miz"],
        theorem=r"theorem\s+(\w+)",
        tactic=r"thus|hence",
        goal=r"theorem.*"
    ),
)

function extract_proofs_from_file(filepath, prover)
    proofs = []
    content = read(filepath, String)
    lines = split(content, '\n')

    pattern = get(PATTERNS, prover, nothing)
    if pattern === nothing
        return proofs
    end

    current_theorem = nothing
    current_goal = nothing
    tactics = String[]

    for line in lines
        line = strip(line)
        isempty(line) && continue
        startswith(line, '#') && continue
        startswith(line, "(*") && continue
        startswith(line, "//") && continue

        # Try to match theorem declaration
        thm_match = match(pattern.theorem, line)
        if thm_match !== nothing
            # Save previous proof if exists
            if current_theorem !== nothing && !isempty(tactics)
                push!(proofs, (
                    prover=prover,
                    theorem=current_theorem,
                    goal=current_goal,
                    tactics=copy(tactics),
                    file=basename(filepath)
                ))
            end

            current_theorem = thm_match.captures[1]
            current_goal = line
            tactics = String[]
        end

        # Try to extract tactics (simple heuristic)
        if current_theorem !== nothing
            # Common tactic keywords
            for keyword in ["intro", "apply", "rewrite", "simpl", "auto",
                           "reflexivity", "induction", "destruct", "split",
                           "unfold", "fold", "exact", "assumption",
                           "simp", "rw", "cases", "have", "show",
                           "by", "using", "from", "with"]
                if occursin(keyword, lowercase(line))
                    push!(tactics, keyword)
                    break
                end
            end
        end
    end

    # Save last proof
    if current_theorem !== nothing && !isempty(tactics)
        push!(proofs, (
            prover=prover,
            theorem=current_theorem,
            goal=current_goal,
            tactics=copy(tactics),
            file=basename(filepath)
        ))
    end

    return proofs
end

function scan_all_proofs()
    all_proofs = []
    proof_stats = Dict{String, Int}()

    @info "Scanning proofs directory: $PROOFS_DIR"

    for (prover, pattern) in PATTERNS
        prover_dir = joinpath(PROOFS_DIR, prover)
        if !isdir(prover_dir)
            continue
        end

        prover_proofs = 0
        for file in readdir(prover_dir)
            filepath = joinpath(prover_dir, file)

            # Check if file matches extension
            matches_ext = any(endswith(file, ext) for ext in pattern.ext)
            if !isfile(filepath) || !matches_ext
                continue
            end

            try
                proofs = extract_proofs_from_file(filepath, prover)
                prover_proofs += length(proofs)
                append!(all_proofs, proofs)

                if !isempty(proofs)
                    @info "  $file: $(length(proofs)) proofs"
                end
            catch e
                @warn "  Failed to parse $file: $e"
            end
        end

        if prover_proofs > 0
            proof_stats[prover] = prover_proofs
        end
    end

    return all_proofs, proof_stats
end

function save_extracted_data(proofs)
    mkpath(OUTPUT_DIR)

    # Save proof states
    open(joinpath(OUTPUT_DIR, "proof_states_v2.jsonl"), "w") do io
        for (i, proof) in enumerate(proofs)
            println(io, "{\"id\":$i,\"prover\":\"$(proof.prover)\",\"goal\":\"$(escape_string(proof.goal))\",\"theorem\":\"$(proof.theorem)\",\"file\":\"$(proof.file)\"}")
        end
    end

    # Save tactics
    open(joinpath(OUTPUT_DIR, "tactics_v2.jsonl"), "w") do io
        tactic_id = 1
        for (i, proof) in enumerate(proofs)
            for tactic in proof.tactics
                println(io, "{\"id\":$tactic_id,\"proof_id\":$i,\"tactic\":\"$(escape_string(tactic))\",\"prover\":\"$(proof.prover)\"}")
                tactic_id += 1
            end
        end
    end

    # Save statistics
    open(joinpath(OUTPUT_DIR, "stats_v2.json"), "w") do io
        stats = Dict(
            "total_proofs" => length(proofs),
            "total_tactics" => sum(length(p.tactics) for p in proofs),
            "unique_theorems" => length(unique(p.theorem for p in proofs)),
            "extraction_date" => string(now()),
            "version" => "v1.3.1-expanded"
        )
        println(io, "{")
        for (i, (k, v)) in enumerate(stats)
            comma = i < length(stats) ? "," : ""
            if v isa String
                println(io, "  \"$k\": \"$v\"$comma")
            else
                println(io, "  \"$k\": $v$comma")
            end
        end
        println(io, "}")
    end

    @info "✓ Saved to $OUTPUT_DIR/"
end

function main()
    @info "ECHIDNA Training Data Extraction v2"
    @info "===================================="
    @info ""

    # Scan all proof files
    proofs, stats = scan_all_proofs()

    @info ""
    @info "Extraction Summary:"
    @info "==================="

    for (prover, count) in sort(collect(stats), by=x->x[2], rev=true)
        @info "  $(rpad(prover, 12)) $count proofs"
    end

    @info ""
    @info "Total: $(length(proofs)) proofs"
    @info "Total tactics: $(sum(length(p.tactics) for p in proofs))"

    # Save data
    if !isempty(proofs)
        save_extracted_data(proofs)
        @info ""
        @info "✓ Extraction complete!"
    else
        @warn "No proofs found!"
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
