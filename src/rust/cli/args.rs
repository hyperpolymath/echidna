// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! `echidna` CLI: args. Moved verbatim from main.rs (hotspot split).

use crate::output::OutputFormat;
use clap::{Parser, Subcommand};
use echidna::ProverKind;
use std::path::PathBuf;

/// Result form of `echidna prove`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, clap::ValueEnum)]
pub(crate) enum ProveOutput {
    /// Human-readable report (the default).
    Human,
    /// One `echidna.prove.result/1` JSON object on stdout.
    Json,
}

/// ECHIDNA - Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance
#[derive(Parser)]
#[command(name = "echidna")]
#[command(version, about, long_about = None)]
#[command(author = "ECHIDNA Project Team")]
pub(crate) struct Cli {
    /// Output format (text, json)
    #[arg(long, global = true, default_value = "text")]
    pub(crate) format: OutputFormat,

    /// Verbose output
    #[arg(short, long, global = true)]
    pub(crate) verbose: bool,

    /// Disable colors
    #[arg(long, global = true)]
    pub(crate) no_color: bool,

    #[command(subcommand)]
    pub(crate) command: Commands,
}

#[derive(Subcommand)]
pub(crate) enum Commands {
    /// Prove a theorem from file
    Prove {
        /// Path to proof file
        file: PathBuf,

        /// Prover to use (auto-detect if not specified)
        #[arg(short, long)]
        prover: Option<ProverKind>,

        /// Timeout in seconds
        #[arg(short, long, default_value = "300")]
        timeout: u64,

        /// Enable neural premise selection
        #[arg(long, default_value = "true")]
        neural: bool,

        /// Prover executable path (override default)
        #[arg(long)]
        executable: Option<PathBuf>,

        /// Library paths
        #[arg(long)]
        library: Vec<PathBuf>,

        /// On failure, run diagnostics and explain why the proof failed
        #[arg(long)]
        diagnose: bool,

        /// Project root for backends with session-based builds (EI-1).
        /// Today: Isabelle uses this to add `-d <root>` to the build
        /// invocation and to import the file's session from the
        /// project's existing ROOT, so theory imports resolve.
        #[arg(long)]
        project_root: Option<PathBuf>,

        /// Sandbox mode for prover invocation (safe-learning b).
        /// One of: none (default), bwrap, podman.
        #[arg(long, default_value = "none")]
        sandbox: String,

        /// Result form. `human` (default) prints the usual report; `json`
        /// prints exactly one `echidna.prove.result/1` object (JCS-canonical
        /// I-JSON) on stdout and sends logs to stderr.
        #[arg(long, value_enum, default_value_t = ProveOutput::Human)]
        output: ProveOutput,
    },

    /// Verify an existing proof
    Verify {
        /// Path to proof file
        file: PathBuf,

        /// Prover to use (auto-detect if not specified)
        #[arg(short, long)]
        prover: Option<ProverKind>,

        /// Timeout in seconds
        #[arg(short, long, default_value = "300")]
        timeout: u64,

        /// Prover executable path (override default)
        #[arg(long)]
        executable: Option<PathBuf>,

        /// Library paths
        #[arg(long)]
        library: Vec<PathBuf>,

        /// On failure, run diagnostics and explain why the proof failed
        #[arg(long)]
        diagnose: bool,
    },

    /// Search theorem libraries
    Search {
        /// Search pattern (regex supported)
        pattern: String,

        /// Prover to search (searches all if not specified)
        #[arg(short, long)]
        prover: Option<ProverKind>,

        /// Maximum results to return
        #[arg(short, long, default_value = "20")]
        limit: usize,
    },

    /// Start interactive REPL mode
    Interactive {
        /// Initial proof file to load
        file: Option<PathBuf>,

        /// Prover to use
        #[arg(short, long)]
        prover: Option<ProverKind>,

        /// Enable neural premise selection
        #[arg(long, default_value = "true")]
        neural: bool,
    },

    /// Start HTTP API server
    Server {
        /// Port to bind to
        #[arg(short, long, default_value = "8081")]
        port: u16,

        /// Host to bind to
        #[arg(long, default_value = "127.0.0.1")]
        host: String,

        /// Enable CORS
        #[arg(long)]
        cors: bool,
    },

    /// List available provers
    ListProvers {
        /// Show detailed information
        #[arg(short, long)]
        detailed: bool,
    },

    /// Show information about a specific prover
    Info {
        /// Prover name
        prover: ProverKind,
    },

    /// Interactive diagnostics REPL for health monitoring
    Diagnostics,

    /// Build / query a project corpus (named decls + dependency DAG)
    Corpus {
        #[command(subcommand)]
        op: CorpusOp,
    },

    /// Mine lexicon candidates across training corpora (flag-only)
    Lexicon {
        #[command(subcommand)]
        op: LexiconOp,
    },

    /// Search proof-design space via simulated annealing
    Design {
        #[command(subcommand)]
        op: DesignOp,
    },

    /// Suggest tactic variants that close a failing lemma
    Suggest {
        /// Target in `<file>:<lemma>` form, e.g. `Foo.thy:bar`
        #[arg(value_name = "TARGET")]
        target: String,

        /// Prover to use (auto-detected from file extension if absent)
        #[arg(short, long)]
        prover: Option<ProverKind>,

        /// Time budget per variant attempt in seconds
        #[arg(long, default_value_t = 60)]
        budget: u64,

        /// Maximum number of variants to report
        #[arg(long, default_value_t = 10)]
        top: usize,

        /// Synonym table directory (defaults to `data/synonyms/`)
        #[arg(long)]
        synonyms_dir: Option<PathBuf>,

        /// Don't run the prover; just print candidate variants
        #[arg(long)]
        dry_run: bool,

        /// Maximum concurrent variant tests
        #[arg(long, default_value_t = 4)]
        max_parallel: usize,
    },
}

#[derive(Subcommand)]
pub(crate) enum CorpusOp {
    /// Walk a project tree and build a corpus index.
    Ingest {
        /// Path to the project root.
        #[arg(short, long)]
        root: PathBuf,
        /// Adapter to use: agda, coq, lean, idris2, acl2_books, creusot,
        /// dafny, fstar, hol4, hol_light, isabelle, metamath, minif2f,
        /// mizar, proofnet, smtlib, spark_ada, tptp, why3, or
        /// hyperpolymath_estate (the multi-repo estate profile).
        #[arg(short, long, default_value = "agda")]
        adapter: String,
        /// Where to write the JSON index. Defaults to
        /// `data/corpus/<basename>.json`.
        #[arg(short, long)]
        out: Option<PathBuf>,
    },
    /// Query a previously-ingested corpus index.
    Query {
        /// Search term (qualified name, short name, or substring).
        pattern: String,
        /// Path to the corpus JSON. Defaults to
        /// `data/corpus/<basename>.json` for the cwd's basename.
        #[arg(short, long)]
        index: Option<PathBuf>,
        /// Show transitive (forward) dependencies of the matched entry.
        #[arg(long)]
        deps: bool,
        /// Show direct reverse-dependencies — entries that reference
        /// the matched name, i.e. things that would (potentially)
        /// break if the matched entry changed.
        #[arg(long)]
        reverse_deps: bool,
        /// Show transitive reverse-closure — full impact set.
        #[arg(long)]
        reverse_closure: bool,
    },
    /// Print summary statistics for a corpus index.
    Stats {
        #[arg(short, long)]
        index: Option<PathBuf>,
    },

    /// Look up entries across every synonym table by `semantic_class`.
    /// Demonstrates cross-prover semantic equivalence: `corpus crossquery
    /// well-foundedness` reports `WellFounded` in Agda, `well_founded` in
    /// Coq, and `WellFounded` in Lean and Idris 2.
    ///
    /// The cross-prover dictionaries are searched too, so classes that
    /// only exist there (`wrapping-arithmetic`, `frame-rule`,
    /// `estate-snif`, or an MSC code such as `68Q60`) resolve.
    Crossquery {
        /// Semantic class to look up (e.g. `well-foundedness`).
        class: String,
        /// Synonym directory (defaults to `data/synonyms`).
        #[arg(long)]
        synonyms_dir: Option<PathBuf>,
        /// Only search the per-prover tables, skipping the cross-prover
        /// dictionaries.
        #[arg(long)]
        provers_only: bool,
    },

    /// Find the K nearest-neighbour entries to a free-form text
    /// query by cosine similarity over the Vector octad embeddings.
    /// The query is canonicalised the same way the corpus is, so a
    /// statement written in one prover's syntax matches entries written
    /// in another's. Useful for "find lemmas structurally near
    /// `WellFounded _<_`".
    Near {
        query: String,
        #[arg(short, long)]
        index: Option<PathBuf>,
        #[arg(short, long, default_value_t = 10)]
        top: usize,
    },

    /// Group matching declarations by their *structural* identity key.
    ///
    /// The key is the SHA-256 of the type's canonical shape — variable
    /// names, module paths, operator spellings and binder keywords are
    /// normalised away — so `+-comm` in Agda, `Nat.add_comm` in Lean and
    /// `eq Nat (add x y) (add y x)` in Dedukti land on one key with no
    /// synonym lookup. `--skeleton` additionally prints the binder- and
    /// sort-free key, which is what provers that elide binders (Isabelle)
    /// match on.
    Identity {
        /// Name pattern to match: a substring of the qualified or short
        /// name, case-insensitive. `*` matches every declaration.
        pattern: String,
        /// Path to the corpus JSON. Defaults to
        /// `data/corpus/<basename>.json` for the cwd's basename.
        #[arg(short, long)]
        index: Option<PathBuf>,
        /// Also print the skeleton key (binders and sorts erased).
        #[arg(long)]
        skeleton: bool,
        /// Only show keys that group declarations from more than one
        /// adapter.
        #[arg(long)]
        cross_only: bool,
    },

    /// Convert a JSON corpus index into 8-modality octad JSONL
    /// (one DeclarationOctad per line). Streamable; compatible with
    /// VeriSim's `/api/v1/octads` endpoint when posted line-by-line.
    ExportOctads {
        /// Path to the JSON corpus index.
        #[arg(short, long)]
        index: PathBuf,
        /// Output JSONL path.
        #[arg(short, long)]
        out: PathBuf,
    },

    /// Load an octad JSONL stream back into a corpus and persist as
    /// JSON. Round-trip is best-effort but lossless for the fields
    /// the corpus cares about (statements, proofs, deps, hazards).
    ImportOctads {
        #[arg(short, long)]
        octads: PathBuf,
        #[arg(short, long)]
        out: PathBuf,
    },
}

#[derive(Subcommand)]
pub(crate) enum LexiconOp {
    /// Pair theorem names and canonical statement shapes across training
    /// corpora and write review candidates as JCS JSON Lines. Every
    /// candidate carries `evidence = none`; `data/synonyms/` is never edited.
    Scan {
        /// Directory holding `proof_states_<corpus>.jsonl` files.
        #[arg(long, default_value = "training_data")]
        training_dir: PathBuf,
        /// A corpus pair, `A:B`. Repeatable; combines with `--preset`.
        #[arg(long = "pair", value_name = "A:B")]
        pairs: Vec<String>,
        /// A named pair set: `learning`, `spanning`, `in-family` or `full`.
        #[arg(long)]
        preset: Option<String>,
        /// Output directory (pairs/, collisions/, summary.jsonl, coverage.jsonl).
        #[arg(long, default_value = "target/lexicon-scan")]
        out: PathBuf,
        /// Also emit pairs whose shared name is generic (`lemma3`, `aux`, `ex1`).
        #[arg(long)]
        keep_generic: bool,
        /// Skip a shared name whose statement cross product exceeds this:
        /// exact pairs per raw name, folded pairs per whole folded group.
        #[arg(long, default_value_t = 64)]
        max_pairs_per_name: usize,
        /// Skip a shape or skeleton group larger than this on either side.
        #[arg(long, default_value_t = 8)]
        max_shape_group: usize,
        /// Key-collision groups to sample per corpus.
        #[arg(long, default_value_t = 40)]
        collision_samples: usize,
    },
}

#[derive(Subcommand)]
pub(crate) enum DesignOp {
    /// Run SA over a named design problem.
    Search {
        /// Problem identifier. Currently: `brouwer-leq` (Phase 1.3
        /// `_≤_` redesign for `Ordinal.Brouwer`).
        problem: String,
        /// Iterations per restart.
        #[arg(long, default_value_t = 1000)]
        iterations: usize,
        /// Number of independent restarts.
        #[arg(long, default_value_t = 4)]
        restarts: usize,
        /// Initial Metropolis temperature.
        #[arg(long, default_value_t = 4.0)]
        temp: f64,
        /// Multiplicative cooling factor per iteration.
        #[arg(long, default_value_t = 0.995)]
        cooling: f64,
        /// Seed.
        #[arg(long, default_value_t = 0xC0FFEE)]
        seed: u64,
        /// Top-K candidates to print.
        #[arg(long, default_value_t = 8)]
        top: usize,
    },

    /// Run a parallel swarm of SA agents with cross-pollination.
    Swarm {
        /// Problem identifier. Currently: `brouwer-leq`.
        problem: String,
        /// Number of parallel agents.
        #[arg(long, default_value_t = 4)]
        agents: usize,
        #[arg(long, default_value_t = 1000)]
        iterations: usize,
        #[arg(long, default_value_t = 4.0)]
        temp: f64,
        #[arg(long, default_value_t = 0.995)]
        cooling: f64,
        #[arg(long, default_value_t = 0xC0FFEE)]
        seed: u64,
        /// Broadcast best-so-far every N iterations.
        #[arg(long, default_value_t = 100)]
        broadcast_every: usize,
        /// Adopt a peer's broadcast only if it beats the agent's best
        /// by this lex-margin (0 = adopt on any improvement).
        #[arg(long, default_value_t = 0)]
        adopt_threshold: i64,
    },
}
