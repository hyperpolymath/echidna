# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Lexicon v2 — the normative schema for every `data/synonyms/*.toml` table.
#
# Owner decision 2026-10-19 (D2): the lexicon schema is written in Nickel.
# The tables stay TOML so the Rust loader (`src/rust/suggest/synonyms.rs`)
# and the Julia mirror (`src/julia/saturation_synonyms.jl`) read them
# unchanged; Nickel imports each table and applies `Table` to it.
# Check one table:   nickel export <<< '(import "data/synonyms/coq.toml") | (import "data/synonyms/schema.ncl").Table'
# Check all tables:  scripts/lexicon-check.sh
#
# Division of labour: this contract checks shape and the cross-field rules
# below. Enum membership of `checked_by` (a `ProverKind` variant name) and
# `format` (an `ExchangeFormat`) is checked by serde when Rust loads the
# table (`tests/lexicon_v2_test.rs` loads every table), so neither list is
# duplicated here.
#
# Design: docs/decisions/2026-10-19-lexicon-v2-and-identity-arbitration.adoc

let fail = fun msg => 'Error { message = msg } in

let is_nonempty_string = fun v => std.is_string v && v != "" in

let all_nonempty_strings = fun v =>
  std.is_array v && std.array.all is_nonempty_string v
in

# `LexiconEvidence::Probe` holds u32 counts; the contract must not certify
# a count the Rust loader rejects.
let is_u32 = fun v =>
  std.is_number v && std.number.is_integer v && v >= 0 && v <= 4294967295
in

let only_fields = fun allowed r =>
  std.array.all (fun f => std.array.elem f allowed) (std.record.fields r)
in

let unknown_fields = fun allowed r =>
  std.array.filter (fun f => !(std.array.elem f allowed)) (std.record.fields r)
in

# How `aliases` relate to `canonical`.
#   synonym         interchangeable names (the v1 meaning; the default)
#   specialisation  each alias is a special case of `canonical`
#   generalisation  each alias generalises `canonical`
#   false_friend    each alias looks like `canonical` and is NOT it; the
#                   variant tester never substitutes it
#   phrase          `canonical` is a multi-token idiom spelled out in `phrase`
let relations = ["synonym", "specialisation", "generalisation", "false_friend", "phrase"] in

# The witness behind a row, mirroring the ECH-05 `FidelityEvidence` shapes.
# Evidence attests the row's relation, whatever it is. It lifts to the
# arbiter only for an identity claim: a `synonym` or `phrase` row whose
# fidelity is not `lossy` (`SynonymEntry::fidelity_evidence` in Rust).
# There `probe` lifts to `DeclaredCorrespondence` and `kernel` to
# `KernelTranslation`; `none` and `curated` (provenance, not fidelity
# evidence) lift to `FidelityEvidence::None`, as does every row that is
# not an identity claim.
let evidence_check = fun value =>
  if !(std.is_record value) || !(std.record.has_field "kind" value) then
    fail "evidence must be a table with a `kind` field"
  else
    let k = value.kind in
    if k == "none" || k == "curated" then
      if only_fields ["kind"] value then 'Ok value
      else fail "evidence `%{k}` takes no other field"
    else if k == "probe" then
      if !(only_fields ["kind", "tests", "failures"] value)
        || !(std.record.has_field "tests" value)
        || !(std.record.has_field "failures" value) then
        fail "probe evidence needs exactly `tests` and `failures`"
      else if !(is_u32 value.tests) || !(is_u32 value.failures) then
        fail "probe evidence `tests` and `failures` must be integers from 0 to 4294967295"
      else if value.tests < 1 || value.failures > value.tests then
        fail "probe evidence needs tests >= 1 and 0 <= failures <= tests"
      else 'Ok value
    else if k == "kernel" then
      if !(only_fields ["kind", "format", "checked_by", "term_hash"] value)
        || !(std.record.has_field "format" value)
        || !(std.record.has_field "checked_by" value)
        || !(std.record.has_field "term_hash" value) then
        fail "kernel evidence needs exactly `format`, `checked_by` and `term_hash`"
      else if !(is_nonempty_string value.format) || !(is_nonempty_string value.checked_by) then
        fail "kernel evidence `format` and `checked_by` must be non-empty strings"
      else if !(std.is_string value.term_hash)
        || !(std.string.is_match "^[0-9a-f]{64}$" value.term_hash) then
        fail "kernel evidence `term_hash` must be 64 lowercase hex digits (BLAKE3)"
      else 'Ok value
    else
      fail "evidence kind must be one of none, curated, probe, kernel"
in

let evidence_contract = std.contract.custom (fun _label value => evidence_check value) in

let entry_fields = [
  "canonical", "aliases", "tactic_class", "semantic_class", "notes", "since", "until",
  "relation", "phrase", "false_friends", "evidence", "fidelity", "residue", "scope",
] in

let optional_strings = ["tactic_class", "semantic_class", "notes", "since", "until"] in

let entry_contract = std.contract.custom (fun _label e =>
  if !(std.is_record e) then fail "each [[synonym]] must be a table"
  else if !(only_fields entry_fields e) then
    fail "unknown field(s): %{std.string.join ", " (unknown_fields entry_fields e)}"
  else if !(std.record.has_field "canonical" e) || !(is_nonempty_string e.canonical) then
    fail "`canonical` must be a non-empty string"
  else if !(std.record.has_field "aliases" e) || !(all_nonempty_strings e.aliases) then
    fail "`%{e.canonical}`: `aliases` must be an array of non-empty strings"
  else if !(std.array.all
      (fun f => !(std.record.has_field f e) || std.is_string (std.record.get f e))
      optional_strings) then
    fail "`%{e.canonical}`: tactic_class, semantic_class, notes, since and until must be strings"
  else
    let relation = if std.record.has_field "relation" e then e.relation else "synonym" in
    if !(std.array.elem relation relations) then
      fail "`%{e.canonical}`: relation must be one of %{std.string.join ", " relations}"
    else if relation == "phrase" && !(std.record.has_field "phrase" e) then
      fail "`%{e.canonical}`: relation `phrase` needs a `phrase` token list"
    else if std.record.has_field "phrase" e && relation != "phrase" then
      fail "`%{e.canonical}`: `phrase` is only allowed with relation `phrase`"
    else if std.record.has_field "phrase" e
      && (!(all_nonempty_strings e.phrase) || std.array.length e.phrase < 2) then
      fail "`%{e.canonical}`: `phrase` must list at least two non-empty tokens"
    else if relation != "synonym" && relation != "phrase" && std.array.length e.aliases == 0 then
      fail "`%{e.canonical}`: relation `%{relation}` needs at least one alias to relate"
    else if std.record.has_field "false_friends" e
      && !(std.is_array e.false_friends
        && std.array.all
          (fun ff => std.is_record ff && only_fields ["name", "table"] ff
            && std.record.has_field "name" ff && is_nonempty_string ff.name
            && std.record.has_field "table" ff && is_nonempty_string ff.table)
          e.false_friends) then
      fail "`%{e.canonical}`: each false_friends item needs exactly a non-empty `name` and `table`"
    else if std.record.has_field "fidelity" e && !(std.array.elem e.fidelity ["exact", "lossy"]) then
      fail "`%{e.canonical}`: fidelity must be `exact` or `lossy`"
    else if std.record.has_field "fidelity" e && e.fidelity == "lossy"
      && !(std.record.has_field "residue" e && is_nonempty_string e.residue) then
      fail "`%{e.canonical}`: a lossy correspondence must say what is lost in `residue`"
    else if std.record.has_field "residue" e
      && !(std.record.has_field "fidelity" e && e.fidelity == "lossy") then
      fail "`%{e.canonical}`: `residue` is only allowed with fidelity `lossy`"
    else if std.record.has_field "scope" e
      && !(std.is_record e.scope && only_fields ["library", "version"] e.scope
        && std.record.has_field "library" e.scope && is_nonempty_string e.scope.library
        && (!(std.record.has_field "version" e.scope) || is_nonempty_string e.scope.version)) then
      fail "`%{e.canonical}`: scope needs a non-empty `library` and optionally a `version`"
    else
      if std.record.has_field "evidence" e then
        evidence_check e.evidence
        |> match {
          'Ok _ => 'Ok e,
          'Error err => fail "`%{e.canonical}`: %{err.message}",
        }
      else
        'Ok e
)
in

{
  Relation = std.contract.from_predicate (fun r => std.array.elem r relations),
  Evidence = evidence_contract,
  Entry = entry_contract,
  Table = { synonym | Array entry_contract },
}
