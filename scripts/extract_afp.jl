#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# extract_afp.jl — Mine the Archive of Formal Proofs (Isabelle/HOL)
# vendored under external_corpora/afp/thys for ECHIDNA training JSONL.
#
# Isabelle was badly under-represented (98 proofs, all from the small
# tropical-resource-typing port). The vendored AFP carries 6,461 .thy
# files — we take a capped sample (~25 per article) so one mega-article
# cannot skew the distribution, while still producing tens of thousands
# of lemmas.
#
# Extraction strategy
# -------------------
# Scan .thy files for top-level keywords
#
#   lemma | theorem | corollary | proposition | schematic_goal
#
# followed by an optional attribute list and an optional name, then:
#
#   1. A quoted statement                 — "... \<Longrightarrow> ..."
#   2. Or an `assumes "..." shows "..."` block.
#
# followed by a proof starting with `by`, `apply`, or `proof ...`.
#
# Output
# ------
#   training_data/proof_states_afp.jsonl
#   training_data/stats_afp.json
#
# ID range: 220000+
#
# Run:  julia scripts/extract_afp.jl

using JSON3
using Dates

const REPO_ROOT        = dirname(dirname(abspath(@__FILE__)))
const AFP_ROOT         = joinpath(REPO_ROOT, "external_corpora", "afp", "thys")
const OUTPUT_DIR       = joinpath(REPO_ROOT, "training_data")
const OUTPUT_FILE      = joinpath(OUTPUT_DIR, "proof_states_afp.jsonl")
const STATS_FILE       = joinpath(OUTPUT_DIR, "stats_afp.json")
const START_ID         = 220000
const MAX_PER_ARTICLE  = 200  # target ~100K+ (893 articles, raw pool 217 593)

# Keyword that introduces a theorem-shaped declaration.
const THM_KW = raw"(?:lemma|theorem|corollary|proposition|schematic_goal)"

# One quoted string, allowing escaped quotes inside.
const QUOTED = raw"\"(?:\\.|[^\"\\])*\""

# Regexes — compiled once.
const NAMED_RE = Regex(
    string(
        "(?m)^\\s*", THM_KW, "\\s+",
        raw"([A-Za-z][A-Za-z0-9_']*)",     # name
        raw"(?:\s*\[[^\]]*\])?",           # optional [simp], [dest!], ...
        raw"\s*:\s*",
    ),
)
const UNNAMED_RE = Regex(
    string("(?m)^\\s*", THM_KW, raw"\s*:?\s*\""),
)
const QUOTED_RE = Regex(QUOTED)
const PROOF_HEAD_RE = r"^\s*(?:by\s|apply\s|proof\s|using\s|unfolding\s|\.\s*$)"

# ---------------------------------------------------------------------------
# Parsing helpers
# ---------------------------------------------------------------------------

"""
    strip_comments(src) -> String

Remove Isabelle line comments (`-- ...` is NOT used; Isabelle uses
`(* ... *)` and text in `⟨...⟩`). We only strip block comments.
"""
function strip_comments(src::AbstractString)::String
    # Fast path if nothing to do.
    occursin("(*", src) || return String(src)
    out = IOBuffer()
    i = firstindex(src)
    n = lastindex(src)
    depth = 0
    while i <= n
        if i < n && src[i] == '(' && src[nextind(src, i)] == '*'
            depth += 1
            i = nextind(src, nextind(src, i))
            continue
        end
        if depth > 0 && i < n && src[i] == '*' && src[nextind(src, i)] == ')'
            depth -= 1
            i = nextind(src, nextind(src, i))
            continue
        end
        if depth == 0
            write(out, src[i])
        end
        i = nextind(src, i)
    end
    return String(take!(out))
end

"""
    collect_quoted_after(src, idx) -> Union{Nothing, Tuple{String, Int}}

Starting at byte index `idx`, skip whitespace and return the next
quoted string (body and the index just past the closing quote). Handles
multi-line quotes.
"""
function collect_quoted_after(src::AbstractString, idx::Int)
    n = lastindex(src)
    # Skip whitespace.
    while idx <= n && isspace(src[idx])
        idx = nextind(src, idx)
    end
    idx <= n || return nothing
    src[idx] == '"' || return nothing
    j = nextind(src, idx)
    while j <= n
        c = src[j]
        if c == '\\' && j < n
            j = nextind(src, nextind(src, j))
            continue
        end
        if c == '"'
            body = src[nextind(src, idx):prevind(src, j)]
            return (String(body), nextind(src, j))
        end
        j = nextind(src, j)
    end
    return nothing
end

"""
    tail_body(src, idx) -> String

Read from `idx` until the next top-level keyword (a line starting with
another theorem-like keyword, `end`, `datatype`, `definition`,
`fun`, `primrec`, etc.). Returns the chunk so we can mine the proof.
"""
function tail_body(src::AbstractString, idx::Int)::String
    remainder = src[idx:end]
    # Cut off at the next top-level boundary.
    cut_re = r"\n(?:lemma|theorem|corollary|proposition|schematic_goal|end|datatype|definition|fun|primrec|theory)\b"
    m = match(cut_re, remainder)
    return m === nothing ? String(remainder) : String(remainder[1:m.offset - 1])
end

"""
    summarise_proof(body) -> String

Pull the first proof chunk — up to the next `qed`, `done`, or 400
chars, whichever comes first. Returned verbatim (may contain Isabelle
escape sequences).
"""
function summarise_proof(body::AbstractString)::String
    trimmed = lstrip(body)
    # Happy path: `by ...`
    m = match(r"^(by\s+(?:\([^()]*\)|[^\n\s]+)(?:[^\n]*))", trimmed)
    m !== nothing && return String(m.match)
    # `apply ... done`
    m = match(r"^(apply\s.*?^done)"m, trimmed)
    m !== nothing && return String(m.match)[1:min(400, lastindex(m.match))]
    # `proof ... qed`
    m = match(r"^(proof.*?^qed)"m, trimmed)
    m !== nothing && return String(m.match)[1:min(400, lastindex(m.match))]
    # Fallback: first line.
    idx_nl = findfirst('\n', trimmed)
    return idx_nl === nothing ? String(trimmed) : String(trimmed[1:prevind(trimmed, idx_nl)])
end

"""
    extract_goal(body) -> Tuple{String, Vector{String}}

Given the body that follows a name-colon, extract the goal statement
and any `assumes` context.
"""
function extract_goal(body::AbstractString)
    assumes = String[]
    goal = ""
    remainder = lstrip(body)

    function _quote_after(s::AbstractString)
        qidx = findfirst('"', s)
        qidx === nothing && return nothing
        return collect_quoted_after(s, qidx)
    end

    # assumes blocks
    while startswith(remainder, "assumes")
        q = _quote_after(remainder)
        q === nothing && break
        push!(assumes, q[1])
        remainder = lstrip(remainder[q[2]:end])
        # Another `and "..."` can follow.
        while startswith(remainder, "and")
            q2 = _quote_after(remainder)
            q2 === nothing && break
            push!(assumes, q2[1])
            remainder = lstrip(remainder[q2[2]:end])
        end
    end

    if startswith(remainder, "shows")
        q = _quote_after(remainder)
        q !== nothing && (goal = q[1]; remainder = remainder[q[2]:end])
    else
        # Plain `"goal"` form.
        q = collect_quoted_after(remainder, firstindex(remainder))
        q !== nothing && (goal = q[1]; remainder = remainder[q[2]:end])
    end

    return (goal, assumes, remainder)
end

# ---------------------------------------------------------------------------
# Per-file extraction
# ---------------------------------------------------------------------------

function parse_file(path::String)::Vector{Dict{String,Any}}
    out = Dict{String,Any}[]
    local raw::String
    try
        raw = read(path, String)
    catch
        return out
    end
    src = strip_comments(raw)

    article = begin
        rel = relpath(path, AFP_ROOT)
        first(splitpath(rel))
    end

    seen = Set{String}()

    # Iterate over all named-theorem matches.
    for m in eachmatch(NAMED_RE, src)
        name = String(m.captures[1])
        body_start = m.offset + sizeof(m.match)
        body_start <= lastindex(src) || continue
        body = tail_body(src, body_start)
        goal, assumes, rest = extract_goal(body)
        isempty(goal) && continue
        proof = summarise_proof(rest)
        key = name * "@" * article
        if !(key in seen)
            push!(seen, key)
            length(goal) > 400 && (goal = goal[1:400] * "…")
            if length(proof) > 400
                proof = proof[1:400] * "…"
            end
            push!(out, Dict{String,Any}(
                "theorem"      => name,
                "goal"         => goal,
                "context"      => assumes,
                "tactic_proof" => proof,
                "source"       => "afp/" * relpath(path, AFP_ROOT),
                "_article"     => article,
            ))
        end
    end

    return out
end

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

function main()
    println("EXTRACT AFP (Isabelle)")
    println("=" ^ 60)
    isdir(AFP_ROOT) || error("Missing $AFP_ROOT — vendor AFP first.")

    files = String[]
    for (root, _, names) in walkdir(AFP_ROOT)
        for n in names
            endswith(n, ".thy") && push!(files, joinpath(root, n))
        end
    end
    println("Scanning $(length(files)) .thy files under AFP")

    per_article = Dict{String, Int}()
    total_raw = 0
    all_recs = Dict{String,Any}[]

    for f in files
        recs = parse_file(f)
        total_raw += length(recs)
        for r in recs
            article = r["_article"]
            if get(per_article, article, 0) < MAX_PER_ARTICLE
                push!(all_recs, r)
                per_article[article] = get(per_article, article, 0) + 1
            end
        end
    end

    println("Raw declarations:         $total_raw")
    println("After per-article cap:    $(length(all_recs))  (cap=$MAX_PER_ARTICLE)")
    println("Articles represented:     $(length(per_article))")

    mkpath(OUTPUT_DIR)
    nid = START_ID
    open(OUTPUT_FILE, "w") do fh
        for rec in all_recs
            delete!(rec, "_article")
            rec["id"]     = nid
            rec["prover"] = "Isabelle"
            JSON3.write(fh, rec)
            println(fh)
            nid += 1
        end
    end
    total = nid - START_ID
    println("Wrote $total records to $OUTPUT_FILE")

    stats = Dict{String,Any}(
        "prover"            => "Isabelle",
        "total_proofs"      => total,
        "files_scanned"     => length(files),
        "articles"          => length(per_article),
        "raw_before_cap"    => total_raw,
        "per_article_cap"   => MAX_PER_ARTICLE,
        "id_range"          => [START_ID, nid - 1],
        "source"            => "external_corpora/afp/thys",
        "extraction_date"   => string(today()),
        "extractor"         => "scripts/extract_afp.jl",
    )
    open(STATS_FILE, "w") do fh
        JSON3.pretty(fh, stats)
    end
    println("Wrote $STATS_FILE")

    println("=" ^ 60)
    println("DONE")
end

main()
