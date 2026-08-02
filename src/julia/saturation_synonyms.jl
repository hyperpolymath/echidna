# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-License-Identifier: MPL-2.0
#
# saturation_synonyms.jl
#
# Reads per-prover synonym TOML tables and the three cross-prover
# dictionaries shipped by the saturation campaign (2026-06-01):
#   data/synonyms/<prover>.toml             — 14 per-prover tables
#   data/synonyms/_msc2020.toml             — MSC2020 cross-walk
#   data/synonyms/_wordnet_math.toml        — WordNet (math senses)
#   data/synonyms/_conceptnet_seed.toml     — ConceptNet seed terms
#
# Schema source of truth: `src/rust/suggest/synonyms.rs` (`SynonymEntry`,
# `SynonymTable`). The Rust loader is the authoritative implementation;
# this module ports just enough of it for the Julia GNN training
# pipeline to apply cross-corpus semantic-class resolution at training
# time. Network-free; offline-only.

"""
    SaturationSynonyms

Loads the 14 per-prover synonym TOML tables plus the three cross-prover
dictionaries (`_msc2020`, `_wordnet_math`, `_conceptnet_seed`) added in
the saturation campaign.

Each entry exposes `(canonical, aliases, tactic_class, semantic_class,
notes, since, until)`. The cross-prover lookup `by_semantic_class`
mirrors `src/rust/suggest/synonyms.rs::SynonymTable::by_semantic_class`
and is the load-bearing primitive for cross-corpus equivalence in the
S5 verification gate.

See `data/synonyms/README.adoc` for the TOML schema and
`docs/decisions/2026-06-01-saturation-campaign.md` for the campaign
that grew the row count from ~863 to ~3,400.
"""
module SaturationSynonyms

using TOML

export load_prover_synonyms,
       load_msc2020,
       load_wordnet_math,
       load_conceptnet_seed,
       by_semantic_class,
       expand_aliases

# ----------------------------------------------------------------------
# Per-prover loader
# ----------------------------------------------------------------------

"""
    load_prover_synonyms(prover::Symbol, dir::String) -> Dict

Load `dir/<prover>.toml` and return a `Dict{String, NamedTuple}` keyed
by the canonical name. Each value is a NamedTuple with fields
`(:aliases, :tactic_class, :semantic_class, :notes, :since, :until)`.

The TOML schema is `[[synonym]]` rows, each with the same fields as
`src/rust/suggest/synonyms.rs::SynonymEntry`. Missing optional fields
default to `nothing` / `String[]`.

The filename mapping follows the Rust `prover_table_filename` helper:
`lean4` → `lean4.toml`, `coq` → `coq.toml`, etc. Pass the prover as
the file's basename (without `.toml`), e.g. `:lean4`, `:isabelle_afp`,
`:hol_light`.

Returns an empty Dict if the file does not exist (matches Rust
`SynonymTable::load` behaviour — missing tables are not an error).
"""
function load_prover_synonyms(prover::Symbol, dir::String)
    path = joinpath(dir, string(prover) * ".toml")
    isfile(path) || return Dict{String,NamedTuple}()

    raw = TOML.parsefile(path)
    rows = get(raw, "synonym", Any[])

    table = Dict{String,NamedTuple}()
    for row in rows
        canonical = String(get(row, "canonical", ""))
        isempty(canonical) && continue
        table[canonical] = (
            aliases = String.(get(row, "aliases", String[])),
            tactic_class = _opt_string(get(row, "tactic_class", nothing)),
            semantic_class = _opt_string(get(row, "semantic_class", nothing)),
            notes = _opt_string(get(row, "notes", nothing)),
            since = _opt_string(get(row, "since", nothing)),
            until = _opt_string(get(row, "until", nothing)),
        )
    end
    return table
end

# ----------------------------------------------------------------------
# Cross-prover dictionaries
# ----------------------------------------------------------------------

"""
    load_msc2020(dir::String) -> Dict

Load `dir/_msc2020.toml` — the Mathematics Subject Classification 2020
cross-prover dictionary. Returns the same Dict shape as
`load_prover_synonyms`, keyed by MSC code (e.g. `"03B05"`,
`"03B70"`).

The MSC dictionary is loaded as a SECONDARY index by
`SynonymTable::with_msc2020()` on the Rust side; downstream training
code merges it into per-prover `semantic_class` resolution to bridge
corpus items across prover taxonomies.

See `data/synonyms/_msc2020.toml` for the wording.
"""
function load_msc2020(dir::String)
    return _load_underscore_table(dir, "_msc2020.toml")
end

"""
    load_wordnet_math(dir::String) -> Dict

Load `dir/_wordnet_math.toml` — the WordNet math-sense dictionary.
Returns the same Dict shape as `load_prover_synonyms`, keyed by the
WordNet lemma (e.g. `"continuity.n.01"`).

Cross-references `src/rust/suggest/synonyms.rs` and the campaign ADR.
"""
function load_wordnet_math(dir::String)
    return _load_underscore_table(dir, "_wordnet_math.toml")
end

"""
    load_conceptnet_seed(dir::String) -> Dict

Load `dir/_conceptnet_seed.toml` — the ConceptNet seed-terms dictionary.
Returns the same Dict shape as `load_prover_synonyms`, keyed by the
seed concept name.

Load-bearing for the offline S5 verification gate (no network access).
"""
function load_conceptnet_seed(dir::String)
    return _load_underscore_table(dir, "_conceptnet_seed.toml")
end

# ----------------------------------------------------------------------
# Cross-table queries
# ----------------------------------------------------------------------

"""
    by_semantic_class(table::Dict, class::String) -> Vector{Tuple{Symbol, String}}

Find every canonical name in `table` whose `semantic_class` field
equals `class`. Returns a vector of `(prover_or_table_tag, canonical)`
pairs.

`table` may be either:
- a single per-prover Dict (from `load_prover_synonyms`), in which case
  the returned tag is `:_anon` for every match (caller knows the
  prover), OR
- a `Dict{Symbol, Dict}` where keys are prover symbols and values are
  per-prover tables — in which case the tag is the prover symbol.

Mirrors `src/rust/suggest/synonyms.rs::SynonymTable::by_semantic_class`
and the cross-prover concatenation pattern documented there.
"""
function by_semantic_class(table::Dict, class::String)
    out = Tuple{Symbol,String}[]
    # Heuristic: if values are NamedTuples we have a single table;
    # if values are Dicts we have a {prover => table} map.
    for (k, v) in table
        if v isa NamedTuple
            if v.semantic_class === class
                push!(out, (:_anon, String(k)))
            end
        elseif v isa AbstractDict
            for (canon, entry) in v
                if entry isa NamedTuple && entry.semantic_class === class
                    push!(out, (Symbol(k), String(canon)))
                end
            end
        end
    end
    return out
end

"""
    expand_aliases(name::String, table::Dict) -> Vector{String}

Given a name (canonical or alias), return every OTHER name in the same
entry. Mirrors `src/rust/suggest/synonyms.rs::SynonymTable::alternatives`.

Returns an empty vector if `name` is not present in `table`. The result
is sorted and de-duplicated to match the Rust contract.
"""
function expand_aliases(name::String, table::Dict)
    out = String[]
    for (canonical, entry) in table
        entry isa NamedTuple || continue
        if String(canonical) == name
            for alias in entry.aliases
                alias == name || push!(out, alias)
            end
        elseif name in entry.aliases
            String(canonical) == name || push!(out, String(canonical))
            for alias in entry.aliases
                alias == name || push!(out, alias)
            end
        end
    end
    sort!(out)
    unique!(out)
    return out
end

# ----------------------------------------------------------------------
# Internal helpers
# ----------------------------------------------------------------------

function _opt_string(v)
    v === nothing && return nothing
    v isa AbstractString || return string(v)
    isempty(v) && return nothing
    return String(v)
end

function _load_underscore_table(dir::String, filename::String)
    path = joinpath(dir, filename)
    isfile(path) || return Dict{String,NamedTuple}()

    raw = TOML.parsefile(path)
    rows = get(raw, "synonym", Any[])

    table = Dict{String,NamedTuple}()
    for row in rows
        canonical = String(get(row, "canonical", ""))
        isempty(canonical) && continue
        table[canonical] = (
            aliases = String.(get(row, "aliases", String[])),
            tactic_class = _opt_string(get(row, "tactic_class", nothing)),
            semantic_class = _opt_string(get(row, "semantic_class", nothing)),
            notes = _opt_string(get(row, "notes", nothing)),
            since = _opt_string(get(row, "since", nothing)),
            until = _opt_string(get(row, "until", nothing)),
        )
    end
    return table
end

end # module SaturationSynonyms
