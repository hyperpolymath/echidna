<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
# Echidna `suggest` — CLI Verb + Variant Tester — Sonnet Handoff Prompt

**Context**: Echidna's `prove` CLI is a one-shot dispatcher. When a proof
fails the user is on their own. The 2026-04-26 ECHIDNA-NOTES failure-mode
analysis (§3) classifies "synonym blindness" and "wrong induction
principle" as two of the ten failure classes a fully-shipped backend
roster doesn't address — and they happen to be the *easiest* class to
solve mechanically with no ML and no creativity. This prompt lays out
exactly that: a new `echidna suggest` verb that takes a failing lemma,
walks a hand-curated synonym table, and reports which substitutions
close the goal.

This is the §4.1 / §4.3 pair from `~/Desktop/ECHIDNA-NOTES-2026-04-27.md`.

**Master plan**: `docs/ROADMAP.md` row 4 ("Every important solver" →
end-state target: real `suggest_tactics` for every backend).

**Prerequisite**: synonym tables seeded at `data/synonyms/{isabelle,coq,lean4}.toml`
(committed 2026-04-27 by Opus, 27 entries; this prompt expands the table
in lockstep with implementation).

**Follows**: §4.4 GNN training. The *next* layer (§4.4) replaces the
hand-curated table with a learned ranker; this layer (§4.1+§4.3) is the
mechanical baseline that the GNN layer must beat to justify itself.

## What this verb does (in one paragraph)

`echidna suggest <file>:<lemma> --prover <P> [--budget 60s]` extracts the
named lemma from the file into a self-contained probe, runs the prover
on the probe to confirm the failure, then for each tactic name in the
probe that appears in `data/synonyms/<P>.toml` it tries every alias and
the canonical form in turn, re-runs the prover, and prints a list of
successful variants ranked by edit minimality. No ML, no search beyond
the table, no creativity. Mechanical, debuggable, and small enough to
fit in 600 LOC.

## Deliverables

### CLI surface (`src/rust/main.rs`)

Add a new variant to the `Commands` enum:

```rust
/// Suggest tactic variants that close a failing lemma
Suggest {
    /// Target in `<file>:<lemma>` form
    #[arg(value_name = "TARGET")]
    target: String,

    /// Prover to use (auto-detect from file extension if absent)
    #[arg(short, long)]
    prover: Option<ProverKind>,

    /// Time budget per variant attempt
    #[arg(long, default_value = "60s")]
    budget: humantime::Duration,

    /// Maximum number of variants to report
    #[arg(long, default_value_t = 10)]
    top: usize,

    /// Synonym table directory (defaults to `data/synonyms/`)
    #[arg(long)]
    synonyms_dir: Option<PathBuf>,

    /// Don't actually run the prover; just print the candidate variants
    #[arg(long)]
    dry_run: bool,
},
```

### New module `src/rust/suggest/`

```
src/rust/suggest/
├── mod.rs              -- public API + CLI dispatch
├── extractor.rs        -- pull a named lemma out of a file (per-prover)
├── synonyms.rs         -- load + index data/synonyms/*.toml
├── variant.rs          -- generate candidate substitutions
├── tester.rs           -- run prover on each variant; classify outcomes
└── report.rs           -- format the result table
```

### `extractor.rs` — per-prover lemma extraction

Five extractors, one per prover the synonym tables cover today:

| Prover | File extension | Lemma syntax we extract |
|---|---|---|
| Isabelle | `.thy` | `lemma <name>: ...` / `theorem <name>: ...` (incl. `proof ... qed` block) |
| Coq | `.v` | `Lemma <name> ...` / `Theorem <name> ...` (incl. proof script up to `Qed.` / `Defined.`) |
| Lean 4 | `.lean` | `theorem <name> ... := by ...` / `lemma <name> ...` |
| Idris2 | `.idr` | `<name> : <type>\n<name> ...` (the function clauses) |
| Agda | `.agda` | similar, definition + clauses |

Each extractor returns a self-contained `Probe` struct:

```rust
pub struct Probe {
    pub prover: ProverKind,
    pub preamble: String,        // imports, opens, declarations the lemma depends on
    pub lemma_source: String,    // the lemma itself, ready to substitute into
    pub tactic_sites: Vec<TacticSite>,  // identified tactic occurrences
}

pub struct TacticSite {
    pub line: usize,             // 1-indexed line within `lemma_source`
    pub col: usize,
    pub name: String,            // e.g. "induct", "omega"
    pub kind: TacticKind,        // TacticName, LemmaRef, RewriteTarget, ...
}
```

Preamble extraction is the hard bit — for first cut, copy the file's
top-of-file `imports` / `Require Import` / `import` block verbatim plus
all definitions that appear before the target lemma in the same file.
Cross-file dependency tracking is **out of scope** for v1.

### `synonyms.rs` — table loader

```rust
pub struct SynonymTable {
    pub entries: Vec<SynonymEntry>,
    /// Index from any name (canonical or alias) to entry indices.
    pub by_name: HashMap<String, Vec<usize>>,
}

pub struct SynonymEntry {
    pub canonical: String,
    pub aliases: Vec<String>,
    pub tactic_class: Option<String>,
    pub notes: Option<String>,
    pub since: Option<String>,
    pub until: Option<String>,
}

impl SynonymTable {
    pub fn load(prover: ProverKind, dir: &Path) -> anyhow::Result<Self> { ... }

    /// Return every other name in the same entry as `name` (canonical + aliases minus self).
    pub fn alternatives(&self, name: &str) -> Vec<String> { ... }
}
```

A name appearing in multiple entries (rare but possible — e.g. `auto`
in both Isabelle and Coq tables) is **kept separate per prover**: the
loader is keyed on `prover`, so cross-prover accidents are impossible.

### `variant.rs` — substitution generator

For each `TacticSite` in the probe, look up alternatives in the table.
Generate one `Variant` per (site, alternative) pair:

```rust
pub struct Variant {
    pub site: TacticSite,
    pub original: String,        // the name we replaced
    pub replacement: String,     // the alternative we tried
    pub probe_source: String,    // full probe with the substitution applied
    pub edit_distance: u32,      // Levenshtein, for ranking
}
```

**Substitution discipline**: replace only at the exact site, not
globally. `induct` may legitimately appear in a comment or string
literal; only AST-level positions count. For v1, accept the
imprecision of substring replacement at the recorded line:col and
document the limitation in `mod.rs`.

**Combinatorics**: do NOT try all combinations of substitutions across
sites. For v1, single-site substitutions only. If the table grows
large enough for combinatorial explosion to bite, gate the multi-site
mode behind `--max-substitutions N`.

### `tester.rs` — variant testing harness

```rust
pub enum VariantOutcome {
    Closes,                      // prover accepted the variant
    Fails(String),               // prover rejected with this error
    Timeout,                     // exceeded --budget
    InvariantSyntax(String),     // probe didn't even parse
}

pub async fn test_variant(
    backend: &dyn ProverBackend,
    variant: &Variant,
    budget: Duration,
) -> VariantOutcome {
    // 1. Write probe_source to a temp file
    // 2. Invoke backend with the temp file
    // 3. Parse the result; classify per VariantOutcome
}
```

**Parallelism**: tests are independent; spawn up to `--max-parallel`
(default 4) concurrent variant tests via `tokio::task::JoinSet`.

**Sandboxing**: each variant test runs in the same sandbox the regular
`prove` pipeline uses (`src/rust/executor/`). No new sandbox
infrastructure needed.

### `report.rs` — output formatter

Output a markdown table to stdout with columns:

| Variant | Site | Outcome | Edit |
|---|---|---|---|
| `induct` → `induction` | line 7 col 12 | ✅ closes | 2 |
| `omega` → `lia` | line 7 col 12 | ✅ closes | 1 |
| `auto` → `force` | line 9 col 5 | ❌ fails | 2 |

Sort: first by `Outcome` (closes > fails > timeout > syntax), then by
edit distance ascending.

When `--dry-run` is set, print the candidate list without an Outcome
column.

## Acceptance criteria

1. **Closes the two ECHIDNA-discovered drifts.** Running
   `echidna suggest tropical-resource-typing/Foo.thy:bar --prover isabelle`
   on a probe that fails because of `induct rule: finite_induct` (the
   2026-04-26 case) reports `induct → induction` as a successful
   variant with edit distance 2.

2. **Closes the `add_le_add → add_mono` drift.** Same setup with the
   monotonicity-name failure case from the 2026-04-26 session.

3. **Handles all five provers** the synonym tables cover. Each prover
   has at least one extractor smoke test in `tests/`.

4. **Sandboxed** — variant testing uses the existing
   `src/rust/executor/` sandbox; no new privilege escalation paths.

5. **Cancellable** — SIGINT cleans up in-flight variant tests.

6. **No ML, no GNN** — the `suggest` verb is mechanical. The GNN
   integration is out of scope; if it appears in this PR, the PR is
   wrong.

7. **Tests** — at minimum:
   - 3 unit tests per extractor (positive, negative, edge case)
   - 1 integration test per prover (full probe→variant→test pipeline,
     with stub backends)
   - 1 end-to-end test using the real Isabelle backend if the CI
     environment has it (`cfg`-gated)

8. **Documentation** — `EXPLAINME.adoc` gets a new section under "How
   ECHIDNA helps you when a proof fails"; `README.adoc` gets a one-line
   pointer.

## Non-goals (Out of scope for v1)

- **Cross-file dependency analysis.** If the lemma uses a fact defined
  in another file, the probe will be missing the dependency and the
  prover will fail with `unknown name`. Document the limitation,
  surface it as a clean error message ("probe missing definition: …
  consider running on a self-contained file"), and move on.

- **GNN-ranked suggestions.** That's §4.4 — different layer, different
  PR, different ranker. This verb is the mechanical baseline.

- **Multi-site combinatorial substitution.** Single-site only for v1.

- **Synonym discovery from corpus.** Manual table only. Mining
  `training_data/` for synonym pairs is a separate item (§4.4
  adjacent).

- **Prover-version detection.** Trust the `--prover` flag. Auto-detect
  by file extension, not by parsing version banners.

## Testing strategy

### Unit (in-tree, fast)

For each prover, hand-craft three probe files:
- `closes-on-canonical/`: lemma works as-written.
- `fails-needs-alias/`: lemma fails until aliased to canonical.
- `unrecoverable/`: lemma fails for a reason the synonym table
  can't fix.

The `tester.rs` should classify each as Closes / Closes-after-substitution / Fails-everything respectively.

### Integration (CI-gated by prover availability)

Per-prover integration test that requires the upstream binary:

```rust
#[tokio::test]
#[cfg(feature = "isabelle-real")]
async fn integration_isabelle_induct_drift() { ... }
```

Add a CI workflow `.github/workflows/suggest-integration.yml` that
provisions Isabelle 2025 and runs the gated tests. Mirror for Coq /
Lean once their integration tests pass locally.

### End-to-end (manual)

Run `echidna suggest` against the actual 2026-04-26 failure cases in
`tropical-resource-typing/`. Both should produce a `Closes` row in the
report.

## Wiring into the existing pipeline

- `dispatch.rs` is **untouched** by this PR — `suggest` is a
  side-channel verb that doesn't use the trust pipeline.
- The variant tester reuses the per-backend `prove()` entry point but
  through a wrapper that classifies prover output as Closes/Fails/etc.
  rather than going through `compute_trust_level`.
- `provers/mod.rs` `suggest_tactics` is a *different* method —
  it returns ML-suggested tactics for an open goal. Keep them separate;
  don't rename either. The `echidna suggest` verb does **not** call
  `suggest_tactics`.

## Synonym table expansion (parallel work for Haiku)

While Sonnet implements the verb, Haiku expands the synonym tables
from the seeded 27 entries to ~50–100 per prover. Haiku prompt
template:

```
Haiku table-expansion, scope = data/synonyms/<prover>.toml

For prover <P>, add hand-curated synonym entries covering:
- Tactic-name drift across the last 3 major versions of <P>
- Lemma-name drift in the standard library / mathlib equivalent
- Common typos / abbreviations (only when they're prover-accepted)

Each entry MUST have:
- canonical (preferred / current name)
- aliases (>= 1)
- notes (rationale or version-specific behaviour)

DO NOT invent synonyms. If you're not confident two names are
interchangeable, skip the entry. Source from upstream changelogs and
release notes; cite in `notes`.

Cap: 30 new entries per session per prover, to keep review tractable.
```

## Failure modes the v1 *won't* catch (and how to know)

The §3 failure-mode analysis classified ten classes; this verb
addresses only:

- **Class 4 (Synonym blindness)** — the headline class.
- **Class 3 (Wrong induction principle)** — partially, when the
  alternative principle is in the synonym table.

Classes 1, 2, 5–10 (wrong abstraction, missing invariant, definition
unfolding choreography, bidirectional gap, cross-domain analogy,
generalization, anti-monotonic information, combinatorial blow-up) are
**not** addressed by this verb and that's fine — they need different
machinery. The §4.5–4.6 plans cover them.

When `echidna suggest` reports "no variants close the goal," the user
should reach for the next layer: `echidna prove --diagnose` (which has
a separate existing diagnostic pipeline) or hand-debug.

## Sequencing

1. (parallel) Sonnet builds `suggest/` module + CLI verb.
2. (parallel) Haiku expands synonym tables to ~100 entries per prover.
3. Sonnet's PR lands first; Haiku's table additions land as separate
   PRs as they accumulate.
4. Once both land, file a usability bug if `suggest` produces zero
   variants on a known-good failure case — the table is too sparse and
   needs more entries.

## Tracking

- This prompt: `docs/handover/SUGGEST-CLI-PROMPT.md`
- Synonym tables: `data/synonyms/{isabelle,coq,lean4}.toml` (committed
  2026-04-27, 27 entries)
- Headline notes: `~/Desktop/ECHIDNA-NOTES-2026-04-27.md` §4.1, §4.2,
  §4.3
- Item #4 in §6 Active Follow-ups
