#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# extract_agda.jl — Mine the locally-vendored Agda standard library
# (external_corpora/agda-stdlib) for proof-shaped declarations and emit
# ECHIDNA-format JSONL.
#
# Agda was the worst-represented prover in the corpus (1 proof of
# 209,517). The stdlib vendored under external_corpora/ carries ~1,260
# .agda files — more than enough to lift Agda out of single-digit
# territory.
#
# Extraction strategy
# -------------------
# Agda top-level declarations follow the shape
#
#     name : Type
#
# where `Type` may span multiple lines. We:
#
#   1. Walk agda-stdlib/src/**/*.agda.
#   2. Skip blank lines, line/block comments, pragmas, module / open /
#      import / private / record / data / syntax / instance directives.
#   3. Accumulate a signature line + its indented continuations.
#   4. Keep a declaration when the signature references proof-relevant
#      Agda constructs: propositional equality `_≡_`, decidable `Dec`,
#      relations (`Rel`, `_≤_`, `_<_`), universally-quantified
#      statements (`∀`, `Π`), `All`, `Any`, `¬`, `⊥`, `⊤`.
#   5. Emit one JSONL record per kept declaration.
#
# Output
# ------
#   training_data/proof_states_agda.jsonl
#   training_data/stats_agda.json
#
# ID range: 210000+
#
# Run:  julia scripts/extract_agda.jl

using JSON3
using Dates

const REPO_ROOT   = dirname(dirname(abspath(@__FILE__)))
const OUTPUT_DIR  = joinpath(REPO_ROOT, "training_data")
const OUTPUT_FILE = joinpath(OUTPUT_DIR, "proof_states_agda.jsonl")
const STATS_FILE  = joinpath(OUTPUT_DIR, "stats_agda.json")
const START_ID    = 210000

# Multiple Agda corpus roots. Added 2026-04-18 (echidna#17): the
# extractor previously walked only agda-stdlib. We now additionally
# ingest agda-cubical (HoTT / cubical type theory) and agda-unimath
# (UniMath's Agda port of univalent foundations) when present. Each
# entry maps (directory → prefix used in source labels).
const AGDA_CORPORA = [
    (joinpath(REPO_ROOT, "external_corpora", "agda-stdlib"),  "agda-stdlib"),
    (joinpath(REPO_ROOT, "external_corpora", "agda-cubical"), "agda-cubical"),
    (joinpath(REPO_ROOT, "external_corpora", "agda-unimath"), "agda-unimath"),
    (joinpath(REPO_ROOT, "external_corpora", "hott-agda"),    "hott-agda"),
]

# Signature-level filters.
const PROOFY = [
    "_≡_", "≡", "_≢_", "≢",
    "Dec ", "Dec.", "Dec(", "Dec{",
    "Rel ", "_≤_", "_<_", "_≥_", "_>_",
    "∀", "Π", "Σ",
    "All ", "Any ",
    "¬", "⊥", "⊤",
    "Reflexive", "Symmetric", "Transitive", "Total",
    "IsCommutative", "IsAssociative", "Injective", "Surjective", "Bijective",
    "Monoid", "Group", "Ring", "Semiring", "Lattice",
    "Homomorphism", "Isomorphism",
]

# Lines we never open a declaration on.
const SKIP_PREFIXES = [
    "module", "open", "import", "private", "abstract", "mutual",
    "syntax", "infix", "infixl", "infixr",
    "record", "data", "postulate", "instance",
    "pattern", "field", "variable", "let", "where",
    "{-", "---", "-- ",
    "{-#", "primitive",
]

const KW_AS_NAME = Set([
    "module", "open", "import", "private", "where", "let", "in",
    "data", "record", "field", "instance", "postulate", "primitive",
    "with", "rewrite", "do", "λ", "forall", "syntax",
    "infix", "infixl", "infixr", "abstract", "mutual",
    "pattern", "variable", "constructor", "hiding", "renaming",
])

# ---------------------------------------------------------------------------
# Parsing
# ---------------------------------------------------------------------------

"""
    line_indent(line) -> Int

Number of leading spaces on `line` (tabs count as 2).
"""
function line_indent(line::AbstractString)::Int
    n = 0
    for c in line
        c == ' ' ? (n += 1) : c == '\t' ? (n += 2) : break
    end
    return n
end

"""
    is_skippable(stripped) -> Bool

True if this trimmed line cannot begin a top-level signature.
"""
function is_skippable(stripped::AbstractString)::Bool
    isempty(stripped) && return true
    for p in SKIP_PREFIXES
        startswith(stripped, p) && return true
    end
    return false
end

"""
    split_signature(line) -> Union{Nothing, Tuple{String, String}}

If `line` parses as `name : body`, return `(name, body)`. Otherwise
return `nothing`. Only accepts a non-indented line.

Colon parsing: take the first ` : ` that is NOT inside parens / braces
and NOT adjacent to `::`.
"""
function split_signature(line::AbstractString)
    depth = 0
    i = firstindex(line)
    while i < lastindex(line)
        c = line[i]
        if c == '(' || c == '{' || c == '['
            depth += 1
        elseif c == ')' || c == '}' || c == ']'
            depth -= 1
        elseif depth == 0 && c == ':' && i > firstindex(line)
            prev = prevind(line, i)
            nxt  = nextind(line, i)
            if line[prev] == ' ' && nxt <= lastindex(line) && line[nxt] == ' '
                # Exclude `::` just in case (Agda uses `:` but be safe).
                nxt2 = nxt <= lastindex(line) ? nxt : lastindex(line)
                if nxt2 <= lastindex(line) && line[nxt2] != ':'
                    name = strip(line[firstindex(line):prev])
                    body = strip(line[nxt:lastindex(line)])
                    return (String(name), String(body))
                end
            end
        end
        i = nextind(line, i)
    end
    return nothing
end

"""
    looks_proofy(sig) -> Bool

True if the signature body references a proof-relevant construct.
"""
function looks_proofy(sig::AbstractString)::Bool
    for kw in PROOFY
        occursin(kw, sig) && return true
    end
    return false
end

"""
    parse_file(path) -> Vector{Dict{String,Any}}

Pull keepable declarations out of one Agda source file.
"""
function parse_file(path::String, corpus_root::String="", corpus_label::String="")::Vector{Dict{String,Any}}
    out = Dict{String,Any}[]
    local lines::Vector{String}
    try
        lines = readlines(path)
    catch
        return out
    end

    i = 1
    n = length(lines)
    seen = Set{String}()
    rel = relpath(path, REPO_ROOT)

    while i <= n
        raw = lines[i]
        stripped = lstrip(raw)

        # Top-level only: skip anything indented or skippable.
        if line_indent(raw) != 0 || is_skippable(stripped)
            i += 1
            continue
        end

        sigparts = split_signature(stripped)
        if sigparts === nothing
            i += 1
            continue
        end
        name, body = sigparts

        # Guard against single-char or keyword "names".
        if isempty(name) || name in KW_AS_NAME || length(name) > 120
            i += 1
            continue
        end
        # Multi-word names (e.g. "f g h") are not proper declarations.
        occursin(' ', name) && (i += 1; continue)

        # Accumulate continuation lines (indented or blank in between).
        buf = [body]
        j = i + 1
        while j <= n
            nxt = lines[j]
            nstripped = lstrip(nxt)
            if isempty(nstripped)
                j += 1; continue
            end
            if line_indent(nxt) > 0
                push!(buf, strip(nstripped))
                j += 1
            else
                break
            end
        end

        sig_body = replace(join(buf, " "), r"\s+" => " ")
        # Bound the recorded signature length to keep JSONL rows compact.
        # Use `first(s, n)` for a character-count slice that is safe
        # against multi-byte UTF-8 (cubical / unimath use many Unicode
        # symbols — `sig_body[1:400]` would crash mid-glyph).
        if length(sig_body) > 400
            sig_body = first(sig_body, 400) * "…"
        end

        # Keep any well-formed top-level signature. The PROOFY gate
        # biased the extraction toward equational proofs, which left
        # Agda under 5K records out of 1,182 files. The signatures we
        # drop otherwise are still useful as training context — they
        # establish definitions that proof-shaped signatures reference.
        key = name * "@" * rel
        if !(key in seen)
            push!(seen, key)
            ctx = collect_context(sig_body)
            push!(out, Dict{String,Any}(
                "theorem" => name,
                "goal"    => sig_body,
                "context" => ctx,
                "source"  => isempty(corpus_label) ?
                    ("agda-stdlib/" * relpath(path, REPO_ROOT)) :
                    (corpus_label * "/" * relpath(path, corpus_root)),
            ))
        end

        i = max(j, i + 1)
    end

    return out
end

"""
    collect_context(sig) -> Vector{String}

Pick up to ten distinctive keywords from the signature so the dataloader
has a non-empty context field to work with.
"""
function collect_context(sig::AbstractString)::Vector{String}
    ctx = String[]
    for kw in (
        "_≡_", "Dec", "Rel", "_≤_", "_<_", "∀", "Π", "Σ",
        "All", "Any", "¬", "⊥", "⊤",
        "Reflexive", "Symmetric", "Transitive",
        "IsCommutative", "Injective", "Surjective",
        "Monoid", "Group", "Ring", "Semiring",
        "Homomorphism", "Isomorphism",
    )
        occursin(kw, sig) && push!(ctx, kw)
        length(ctx) >= 10 && break
    end
    return ctx
end

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

function main()
    println("EXTRACT AGDA")
    println("=" ^ 60)

    # Walk every Agda corpus that is present on disk. At least one
    # must exist — agda-stdlib remains the canonical minimum.
    corpus_file_lists = Tuple{String,String,Vector{String}}[]
    for (corpus_root, corpus_label) in AGDA_CORPORA
        isdir(corpus_root) || continue
        these = String[]
        for (root, _, names) in walkdir(corpus_root)
            for n in names
                if endswith(n, ".agda") || endswith(n, ".lagda.md")
                    push!(these, joinpath(root, n))
                end
            end
        end
        push!(corpus_file_lists, (corpus_root, corpus_label, these))
        println("  $(corpus_label): $(length(these)) files under $(corpus_root)")
    end
    if isempty(corpus_file_lists)
        error("No Agda corpora found — vendor agda-stdlib (minimum) first.")
    end
    total_files = sum(length(xs[3]) for xs in corpus_file_lists)
    println("Scanning $(total_files) Agda source files across $(length(corpus_file_lists)) corpora")

    all_records = Dict{String,Any}[]
    parsed_ok = 0
    for (corpus_root, corpus_label, files) in corpus_file_lists
        corpus_start = length(all_records)
        for f in files
            recs = parse_file(f, corpus_root, corpus_label)
            if !isempty(recs)
                parsed_ok += 1
                append!(all_records, recs)
            end
        end
        println("  $(corpus_label): $(length(all_records) - corpus_start) declarations kept")
    end
    println("Files with keepable decls: $parsed_ok")
    println("Raw declarations:          $(length(all_records))")

    # Assign IDs and write JSONL.
    mkpath(OUTPUT_DIR)
    nid = START_ID
    open(OUTPUT_FILE, "w") do fh
        for rec in all_records
            rec["id"]           = nid
            rec["prover"]       = "Agda"
            rec["tactic_proof"] = ""  # Agda stdlib uses equational proofs;
                                      # the body lives in the source file
                                      # referenced in rec["source"].
            JSON3.write(fh, rec)
            println(fh)
            nid += 1
        end
    end
    total = nid - START_ID
    println("Wrote $total records to $OUTPUT_FILE")

    # Stats.
    stats = Dict{String,Any}(
        "prover"          => "Agda",
        "total_proofs"    => total,
        "files_scanned"   => total_files,
        "files_with_proofs" => parsed_ok,
        "id_range"        => [START_ID, nid - 1],
        "corpora"         => [label for (_root, label) in AGDA_CORPORA if isdir(_root)],
        "extraction_date" => string(today()),
        "extractor"       => "scripts/extract_agda.jl",
    )
    open(STATS_FILE, "w") do fh
        JSON3.pretty(fh, stats)
    end
    println("Wrote $STATS_FILE")

    println("=" ^ 60)
    println("DONE")
end

main()
