<!--
SPDX-License-Identifier: MPL-2.0
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->

# Cross-Repo Proof Dependency DAG

**Status**: Design draft — implementation not yet started.
**Closes**: estate blocker **C14** from the 2026-06-03 audit
("when ephapax `formal/` changes, downstream consumers don't re-verify").

---

## Problem

The estate carries several producer/consumer proof relationships that
the current per-repo CI shape does not honour:

| Producer        | Path                          | Known consumers                                   |
|-----------------|-------------------------------|---------------------------------------------------|
| `ephapax`       | `formal/PRESERVATION-*.v`     | `valence-shell`, `verisimdb`, `proven`            |
| `echo-types`    | `formal/echo/*.v`             | `ephapax` (L3 obligations), `valence-shell`       |
| `kategoria`     | `formal/*.v`                  | `verisimdb`, downstream HP type-checker repos     |
| `tropical-resource-typing` | `formal/*.v`        | `verisimdb` (Q1 foundation)                       |
| `vcl-ut`        | `formal/*.v`                  | `verisimdb` (P3, V2 foundation pack)              |

Today, when a producer's proofs change, no automatic signal walks the
DAG to re-verify downstream. Transitive correctness drift goes
unnoticed until a manual reviewer notices, or until a consumer's own CI
happens to re-run against the new producer SHA. That can be weeks.

This is **C14** in the 2026-06-03 audit's punch list.

---

## Scope (this doc) vs out-of-scope

In-scope:
- Where the DAG lives.
- Edge format (TOML / A2ML).
- Edge-discovery rules (manual + automatic).
- Trigger semantics (which webhook fires which downstream jobs).
- Failure semantics (degraded mode when a consumer can't be reached).

Out-of-scope:
- Term-level proof translation between Coq ↔ Lean ↔ Agda — that is
  cross-prover canonicalisation, blocked on `verisimdb#3`.
- Per-theorem dependency tracking (i.e. "only re-verify proofs whose
  imports actually touched the producer hunk"). v1 is repo-grain only;
  per-theorem precision is a follow-up once the v1 plumbing is real.

---

## Where the DAG lives

**Recommendation: edges declared per-consumer; aggregation in echidna.**

```text
  consumer repo                           echidna (estate dispatcher)
  ─────────────                           ─────────────────────────────
  .machine_readable/                      ┌─────────────────┐
    proof-deps.a2ml ───── ingest ───────► │ proof_dag.toml  │
                                          │ (synthesised    │
  consumer repo                           │  per-fetch)     │
  ─────────────                           │                 │
  .machine_readable/                      └─────────┬───────┘
    proof-deps.a2ml ───── ingest ───────►           │
                                                    ▼
                                          ┌─────────────────┐
                                          │ hypatia         │
                                          │ (push fixes /   │
                                          │ enqueue jobs)   │
                                          └─────────┬───────┘
                                                    │
                                                    ▼
                                          ┌─────────────────┐
                                          │ echidnabot      │
                                          │ (per-repo CI)   │
                                          └─────────────────┘
```

Rationale:

- **Edges live in the consumer**, not the producer. Producers shouldn't
  need to know who depends on them; the reverse direction (consumer
  declares what it pulls from) matches how Coq/Lean/Agda imports already
  work and means no producer-side coordination is needed when a new
  consumer onboards.
- **Aggregation in echidna** because echidna is already the estate's
  prover-aware dispatcher (`src/rust/provers/`, prover-class scheduling,
  trust-bridge), and the dispatch decision needs prover metadata that
  echidnabot doesn't carry.
- **Trigger orchestration in hypatia** because hypatia is the estate-CI
  intelligence layer that already coordinates `gitbot-fleet` and the
  "push committed fixes to remotes" contract (see the C15 PR).

---

## Edge format

A new file `proof-deps.a2ml` joins the existing
`.machine_readable/bot_directives/` family:

```toml
# .machine_readable/proof-deps.a2ml
schema_version = "1.0"
directive_type = "proof-deps"

# Each [[depends_on]] entry is one edge from this consumer to a producer.
[[depends_on]]
producer   = "hyperpolymath/ephapax"
ref        = "main"                       # branch | tag | exact-sha
paths      = ["formal/PRESERVATION-*.v"]  # producer-side globs
local_uses = ["formal/L3-ECHO/**/*.v"]    # consumer-side proofs that
                                          # transitively rely on producer
rationale  = "L3 echo obligations re-use ephapax's preservation_l3."
# Optional gating override:
fail_open  = false   # if true: producer red doesn't block consumer CI
                     # (default false — producer red ⇒ consumer red).

[[depends_on]]
producer   = "hyperpolymath/echo-types"
ref        = "main"
paths      = ["formal/echo/*.v"]
local_uses = ["formal/L3-ECHO/EchoAxioms.v"]
rationale  = "Echo-types canonical axioms; echo-types audit recorded."
```

Schema notes:

- `producer` is `<owner>/<repo>` — platform-agnostic; same shape works
  for Codeberg / Radicle once those adapters land.
- `ref` is normally `main`; per-edge SHA pins are allowed for
  reproducibility-critical consumers (e.g. release branches).
- `paths` are producer-side globs — used both for edge invalidation
  ("did this hunk touch a tracked path?") and for the v2 per-theorem
  story.
- `local_uses` documents *why* the edge exists. Mostly for humans, but
  hypatia surfaces it in the PR comment so reviewers know what failed.
- Tolerance: unknown fields are ignored. Same forward-compat shape as
  the C12 manifest.

---

## Discovery

Two discovery paths feed the DAG:

1. **Manual** — author commits `proof-deps.a2ml` declaring producers.
   This is the only path that v1 honours.
2. **Automatic** (v2, after `verisimdb#3`) — extract producer references
   from Coq `Require Import`, Lean `import`, Agda `open import`. The
   estate's per-language imports vary too widely to do this safely in
   v1; a missing edge surfaces as a stale-proof failure within one
   producer-change cycle and the author adds it manually.

The aggregator (`echidna ingest-proof-deps`) walks each repo's
`proof-deps.a2ml` via the same `PlatformAdapter::get_file_contents` path
echidnabot already uses for `bot_directives/echidnabot.a2ml`. Edges are
cached for 24h with ETag revalidation. No edge → no behaviour change.

---

## Trigger semantics

```text
  producer push to tracked path
            │
            ▼
  webhook hits echidna  ─────► consult ingested DAG, find consumers
            │                       (forward edges by `paths` glob match)
            ▼
  for each consumer:
    enqueue echidnabot job
       payload: { repo, ref, reason: "upstream change",
                  upstream: { producer, sha, paths } }
            │
            ▼
  echidnabot runs that repo's proof check (per C12 manifest)
            │
            ▼
  result → comment on producer commit + open / update consumer issue
       "ephapax@abc1234 broke valence-shell@formal/L3-ECHO/EchoAxioms.v"
```

Trigger details:

- Path-grained: only producers' commits that touch a tracked `paths`
  glob fan out. Touching producer README, CI, or non-tracked source
  does not enqueue anything.
- Coalesced: multiple pushes within a 60s window collapse to one
  downstream job per consumer.
- Backpressure: hypatia's existing concurrency limits (per-repo
  semaphore + global cap) apply. Cascade fan-out is bounded.
- Fail-open: if echidna's DAG cache is stale or unreachable, fall back
  to "no edges" — never block producer CI on the dispatcher being down.

---

## Failure semantics

| Condition                                  | Behaviour                                  |
|--------------------------------------------|--------------------------------------------|
| Consumer's `proof-deps.a2ml` is malformed  | Log warning; treat as "no edges". No CI block on the consumer. |
| Producer ref not reachable (deleted branch / private repo) | Edge skipped; warning surfaced in the consumer's next PR. |
| Consumer CI red after upstream-triggered run | Issue opened in consumer repo, label `blocked-on:<producer>#<sha>`; `fail_open` overrides this to advisory-only. |
| Producer red + `fail_open = false`         | Consumer's `merge_block` (per C12 manifest) gates merges to consumer-main. |
| DAG cycle (A → B → A)                      | Detected at ingest; cycle edge dropped + filed as `echidna#<issue>` with both repos labelled. v1 logs only; v2 hard-fails ingestion. |

---

## Concrete walk-through

```text
2026-06-XX  10:00  ephapax main pushes commit abc1234
                    touching formal/PRESERVATION-L3.v

           10:00:02 echidna webhook receives push event
                    matches DAG glob "formal/PRESERVATION-*.v"
                    consumers: { valence-shell, verisimdb, proven }

           10:00:03 hypatia enqueues 3 echidnabot jobs:
                    valence-shell @ main  (proof-set: formal/L3-ECHO/**/*.v)
                    verisimdb     @ main  (proof-set: formal/foundation-pack/**)
                    proven        @ main  (proof-set: formal/echo-leak/*.v)

           10:00:08 echidnabot dispatches Coq jobs (per each repo's
                    C12 manifest provers list)

           10:01:42 results land:
                    valence-shell GREEN
                    verisimdb     RED  (preservation_l3 fails on L2-modality lemma)
                    proven        GREEN

           10:01:44 echidna posts comment on ephapax abc1234:
                    "Downstream impact: verisimdb red — preservation_l3 fails
                     against L2-modality lemma at line 412."
                    Opens issue verisimdb#NNN with full diff + the failing
                    proof excerpt. Adds label "blocked-on:ephapax@abc1234".
```

---

## Open decisions for the owner

1. **Edge ref policy**: do all consumers default to `ref = "main"`, or
   should release-branch consumers be required to pin a SHA? Tradeoff:
   pinned SHAs are reproducible but go stale; `main` is current but can
   silently flip.
2. **Issue spam vs PR comment**: when a producer's main breaks a
   consumer, do we open an issue per consumer (high signal, can pile
   up) or just comment on the producer commit (no follow-up nudge)?
3. **Echo-types special case**: echo-types is the L3 canonical axioms
   producer for ephapax (per estate policy
   [[feedback_proofs_must_check_and_cross_doc_echo_types]]). Should
   echo-types ↔ ephapax edges be auto-injected by echidna without a
   `proof-deps.a2ml` declaration, or stay opt-in like everything else?
4. **`fail_open` default**: producer red ⇒ consumer red is the safer
   default but it means an upstream's bad-day red-CI cascades. Should
   `fail_open = true` be the default and `fail_open = false` be the
   opt-in for hard-coupled consumers?

---

## What this design unblocks

Closing C14 makes three other audit blockers more tractable:

- **C16** (GNN outcome-feedback loop) — per-edge success/failure
  signals are exactly the cross-repo training data the GNN currently
  doesn't see.
- **F25** (cross-prover RDF alignment, blocked on `verisimdb#3`) — the
  DAG gives an empirical ground-truth set of co-evolving proof pairs,
  which is the input that translation work needs.
- **D22** (no single green "trust pipeline verified" badge) — the DAG
  defines what "fully verified estate" means: every edge green.

---

## Acceptance criteria for the implementation PR (out of scope here)

When this design is implemented:

- [ ] `echidna ingest-proof-deps` walks all repos that echidna already
      knows about, parses any `.machine_readable/proof-deps.a2ml`,
      and builds `proof_dag.toml` at the daemon level.
- [ ] Producer webhooks fan out via `EdgeEnvelope` events on the
      existing `dispatch.rs` channel.
- [ ] hypatia's enqueue path accepts `EdgeEnvelope` and routes to
      echidnabot exactly as it does for direct-push events.
- [ ] Cycle detection runs at ingest and logs (v1) / hard-fails (v2).
- [ ] Three estate-shaped fixtures: ephapax→valence-shell,
      echo-types→ephapax, kategoria→verisimdb.
- [ ] Sad-path: unreachable producer ref, malformed `proof-deps.a2ml`,
      consumer mid-rebase. All degrade gracefully.

---

## See also

- C12 PR — per-repo manifest schema v2.0 (echidnabot).
- C15 PR — hypatia push-fixes wiring (gitbot-fleet).
- `docs/architecture/CORRECTNESS-ARCHITECTURE.md` — the soundness
  invariant the DAG must not violate.
- `docs/architecture/VERISIM-ER-SCHEMA.md` — where ingested edges
  eventually persist for cross-prover analytics.
