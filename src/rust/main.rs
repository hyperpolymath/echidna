// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: PMPL-1.0-or-later

//! ECHIDNA CLI - Main binary entry point
//!
//! Provides command-line interface, REPL, and HTTP server for theorem proving

use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use echidna::dispatch::ProverDispatcher;
use echidna::{
    diagnostics::proof_failure::diagnose_from_outcome, provers::ProverBackend, ProverConfig,
    ProverKind,
};
use indicatif::{ProgressBar, ProgressStyle};
use std::sync::Arc;
use std::path::PathBuf;
use tracing::{info, warn};

mod output;
mod repl;
mod server;

use output::{OutputFormat, OutputFormatter};
use repl::DiagnosticsREPL;

/// ECHIDNA - Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance
#[derive(Parser)]
#[command(name = "echidna")]
#[command(version, about, long_about = None)]
#[command(author = "ECHIDNA Project Team")]
struct Cli {
    /// Output format (text, json)
    #[arg(long, global = true, default_value = "text")]
    format: OutputFormat,

    /// Verbose output
    #[arg(short, long, global = true)]
    verbose: bool,

    /// Disable colors
    #[arg(long, global = true)]
    no_color: bool,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
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
enum CorpusOp {
    /// Walk a project tree and build a corpus index.
    Ingest {
        /// Path to the project root.
        #[arg(short, long)]
        root: PathBuf,
        /// Adapter to use (currently only `agda`).
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
        /// Show transitive dependencies of the matched entry.
        #[arg(long)]
        deps: bool,
    },
    /// Print summary statistics for a corpus index.
    Stats {
        #[arg(short, long)]
        index: Option<PathBuf>,
    },
}

#[derive(Subcommand)]
enum DesignOp {
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

#[tokio::main]
async fn main() -> Result<()> {
    // Parse CLI arguments
    let cli = Cli::parse();

    // Initialize tracing
    init_tracing(cli.verbose);

    // Disable colors if requested
    if cli.no_color {
        colored::control::set_override(false);
    }

    // Create output formatter
    let formatter = OutputFormatter::new(cli.format);

    // Execute command
    match cli.command {
        Commands::Prove {
            file,
            prover,
            timeout,
            neural,
            executable,
            library,
            diagnose,
            project_root,
            sandbox,
        } => {
            prove_command(
                file, prover, timeout, neural, executable, library, diagnose,
                project_root, sandbox, &formatter,
            )
            .await?;
        },

        Commands::Verify {
            file,
            prover,
            timeout,
            executable,
            library,
            diagnose,
        } => {
            verify_command(file, prover, timeout, executable, library, diagnose, &formatter).await?;
        },

        Commands::Search {
            pattern,
            prover,
            limit,
        } => {
            search_command(pattern, prover, limit, &formatter).await?;
        },

        Commands::Interactive {
            file,
            prover,
            neural,
        } => {
            interactive_command(file, prover, neural).await?;
        },

        Commands::Server { port, host, cors } => {
            server_command(port, host, cors).await?;
        },

        Commands::ListProvers { detailed } => {
            list_provers_command(detailed, &formatter)?;
        },

        Commands::Info { prover } => {
            info_command(prover, &formatter)?;
        },

        Commands::Diagnostics => {
            diagnostics_command().await?;
        },
        Commands::Corpus { op } => {
            corpus_command(op, &formatter)?;
        },

        Commands::Design { op } => {
            design_command(op, &formatter).await?;
        },

        Commands::Suggest {
            target,
            prover,
            budget,
            top,
            synonyms_dir,
            dry_run,
            max_parallel,
        } => {
            let synonyms_dir = synonyms_dir.unwrap_or_else(|| PathBuf::from("data/synonyms"));
            let config = echidna::suggest::SuggestConfig {
                target,
                prover,
                budget: std::time::Duration::from_secs(budget),
                top,
                synonyms_dir,
                dry_run,
                max_parallel,
            };
            echidna::suggest::run(config).await?;
        },
    }

    Ok(())
}

/// Initialize tracing/logging
fn init_tracing(verbose: bool) {
    use tracing_subscriber::filter::EnvFilter;
    use tracing_subscriber::{fmt, prelude::*};

    let filter = if verbose {
        EnvFilter::new("echidna=debug,info")
    } else {
        EnvFilter::new("echidna=info,warn")
    };

    tracing_subscriber::registry()
        .with(filter)
        .with(fmt::layer())
        .init();
}

/// Prove command implementation
async fn prove_command(
    file: PathBuf,
    prover_kind: Option<ProverKind>,
    timeout: u64,
    neural: bool,
    executable: Option<PathBuf>,
    library: Vec<PathBuf>,
    diagnose: bool,
    project_root: Option<PathBuf>,
    sandbox: String,
    formatter: &OutputFormatter,
) -> Result<()> {
    info!("Starting proof for: {}", file.display());

    let kind = detect_prover(prover_kind, &file)?;
    let config = create_config(
        kind, timeout, neural, executable, library, project_root, &sandbox,
    )?;
    let prover = echidna::provers::ProverFactory::create(kind, config)
        .context("Failed to create prover backend")?;

    let pb = create_progress_bar("Parsing proof file...");
    let state = prover
        .parse_file(file.clone())
        .await
        .context("Failed to parse proof file")?;

    pb.set_message("Verifying proof...");
    let result = prover
        .verify_proof(&state)
        .await
        .context("Failed to verify proof")?;
    pb.finish_and_clear();

    if result {
        formatter.success(&format!(
            "✓ Proof verified successfully for {}",
            file.display()
        ))?;
        formatter.output_proof_state(&state)?;
    } else {
        formatter.error(&format!(
            "✗ Proof verification failed for {}",
            file.display()
        ))?;
        formatter.output_proof_state(&state)?;
        if diagnose {
            emit_diagnostic(kind, &*prover, &state, formatter).await;
        }
        std::process::exit(1);
    }

    Ok(())
}

/// Run `check()` on the prover and display a structured diagnostic report.
///
/// Called after a failed `verify_proof()` when `--diagnose` is active.
/// Uses the richer `ProverOutcome` returned by `check()` to produce an
/// actionable report via `diagnose_from_outcome`.
async fn emit_diagnostic(
    kind: ProverKind,
    prover: &dyn ProverBackend,
    state: &echidna::core::ProofState,
    formatter: &OutputFormatter,
) {
    let outcome = match prover.check(state).await {
        Ok(o) => o,
        Err(e) => {
            let _ = formatter.error(&format!("[diagnose] could not run check(): {}", e));
            return;
        },
    };
    let report = diagnose_from_outcome(kind, &outcome);
    let _ = formatter.info("\n--- Proof Failure Diagnostic ---");
    let _ = formatter.info(&report.display());
}

/// Verify command implementation
async fn verify_command(
    file: PathBuf,
    prover_kind: Option<ProverKind>,
    timeout: u64,
    executable: Option<PathBuf>,
    library: Vec<PathBuf>,
    diagnose: bool,
    formatter: &OutputFormatter,
) -> Result<()> {
    info!("Verifying proof: {}", file.display());

    let kind = detect_prover(prover_kind, &file)?;
    let config = create_config(kind, timeout, true, executable, library, None, "none")?;
    let prover = echidna::provers::ProverFactory::create(kind, config)
        .context("Failed to create prover backend")?;

    let pb = create_progress_bar("Parsing proof file...");
    let state = prover
        .parse_file(file.clone())
        .await
        .context("Failed to parse proof file")?;

    pb.set_message("Verifying proof...");
    let result = prover
        .verify_proof(&state)
        .await
        .context("Failed to verify proof")?;
    pb.finish_and_clear();

    if result {
        formatter.success(&format!("✓ Proof is valid: {}", file.display()))?;
        formatter.info(&format!("Goals: {}", state.goals.len()))?;
        formatter.info(&format!("Tactics: {}", state.proof_script.len()))?;
        formatter.info(&format!(
            "Theorems in context: {}",
            state.context.theorems.len()
        ))?;
    } else {
        formatter.error(&format!("✗ Proof is invalid: {}", file.display()))?;
        if diagnose {
            emit_diagnostic(kind, &*prover, &state, formatter).await;
        }
        std::process::exit(1);
    }

    Ok(())
}

/// Search command implementation
async fn search_command(
    pattern: String,
    prover_kind: Option<ProverKind>,
    limit: usize,
    formatter: &OutputFormatter,
) -> Result<()> {
    info!("Searching for: {}", pattern);

    let provers: Vec<ProverKind> = if let Some(kind) = prover_kind {
        vec![kind]
    } else {
        // Search all provers
        vec![
            ProverKind::Agda,
            ProverKind::Coq,
            ProverKind::Lean,
            ProverKind::Isabelle,
            ProverKind::Z3,
            ProverKind::CVC5,
            ProverKind::Metamath,
            ProverKind::HOLLight,
            ProverKind::Mizar,
            ProverKind::PVS,
            ProverKind::ACL2,
            ProverKind::HOL4,
            ProverKind::Idris2,
        ]
    };

    formatter.info(&format!(
        "Searching {} prover(s) for pattern: {}",
        provers.len(),
        pattern
    ))?;

    let mut total_results = 0;

    for kind in provers {
        let config = ProverConfig::default();

        if let Ok(prover) = echidna::provers::ProverFactory::create(kind, config) {
            formatter.section(&format!("\n{:?} Results:", kind))?;

            match prover.search_theorems(&pattern).await {
                Ok(results) => {
                    total_results += results.len();

                    for (i, result) in results.iter().take(limit).enumerate() {
                        formatter.result(&format!("  {}. {}", i + 1, result))?;
                    }

                    if results.len() > limit {
                        formatter
                            .info(&format!("  ... and {} more results", results.len() - limit))?;
                    }
                },
                Err(e) => {
                    warn!("Failed to search {}: {}", kind, e);
                },
            }
        }
    }

    // After per-backend search, add a cross-prover layer: query VeriSimDB
    // for matches across every prover that has ever recorded an attempt.
    // This compensates for backends without a native search command (the
    // 70+ that legitimately return Vec::new() because their underlying
    // prover doesn't ship a `Search`-equivalent). No-op without the
    // `verisim` feature; logs and continues on Verisim outage.
    let verisim_url = std::env::var("VERISIM_URL")
        .unwrap_or_else(|_| "http://localhost:8080".to_string());
    match echidna::vcl_ut::cross_prover_search_names(&verisim_url, &pattern, limit).await {
        Ok(cross) if !cross.is_empty() => {
            formatter.section("\nCross-prover (VeriSimDB) Results:")?;
            total_results += cross.len();
            for (i, result) in cross.iter().take(limit).enumerate() {
                formatter.result(&format!("  {}. {}", i + 1, result))?;
            }
            if cross.len() > limit {
                formatter.info(&format!("  ... and {} more results", cross.len() - limit))?;
            }
        }
        Ok(_) => {}
        Err(e) => {
            warn!("Cross-prover search failed: {}", e);
        }
    }

    formatter.info(&format!("\nTotal results found: {}", total_results))?;

    Ok(())
}

/// Interactive REPL command
async fn interactive_command(
    file: Option<PathBuf>,
    prover_kind: Option<ProverKind>,
    neural: bool,
) -> Result<()> {
    info!("Starting interactive REPL mode");

    repl::start_repl(file, prover_kind, neural).await
}

/// HTTP Server command
async fn server_command(port: u16, host: String, cors: bool) -> Result<()> {
    info!("Starting HTTP server on {}:{}", host, port);

    server::start_server(port, host, cors).await
}

/// List provers command
fn list_provers_command(detailed: bool, formatter: &OutputFormatter) -> Result<()> {
    let provers = ProverKind::all();

    formatter.header("Available Provers")?;
    formatter.info(&format!("Total: {} provers\n", provers.len()))?;

    for prover in provers {
        let tier = prover.tier();
        let complexity = prover.complexity();
        let time = prover.implementation_time();

        if detailed {
            formatter.section(&format!("{:?}", prover))?;
            formatter.info(&format!("  Tier: {}", tier))?;
            formatter.info(&format!("  Complexity: {}/5", complexity))?;
            formatter.info(&format!("  Implementation time: {} weeks", time))?;
            formatter.info("")?;
        } else {
            formatter.result(&format!(
                "{:12} - Tier {} | Complexity {}/5 | {} weeks",
                format!("{:?}", prover),
                tier,
                complexity,
                time
            ))?;
        }
    }

    if !detailed {
        formatter.info("\nUse --detailed flag for more information")?;
    }

    Ok(())
}

/// Info command - show detailed information about a prover
fn info_command(prover: ProverKind, formatter: &OutputFormatter) -> Result<()> {
    formatter.header(&format!("{:?} Prover Information", prover))?;
    formatter.info("")?;

    formatter.section("Classification")?;
    formatter.info(&format!("  Tier: {}", prover.tier()))?;
    formatter.info(&format!("  Complexity: {}/5", prover.complexity()))?;
    formatter.info(&format!(
        "  Implementation time: {} weeks",
        prover.implementation_time()
    ))?;
    formatter.info("")?;

    formatter.section("Description")?;
    let description = match prover {
        ProverKind::Agda => {
            "Dependently typed functional programming language and proof assistant.\n  \
             Tier 1 prover. Strong type system with universe polymorphism."
        },
        ProverKind::Coq => {
            "Interactive theorem prover using the Calculus of Inductive Constructions.\n  \
             Widely used in formal verification and mathematics. Powerful tactic language."
        },
        ProverKind::Lean => {
            "Modern theorem prover and programming language with dependent types.\n  \
             Strong community, extensive mathlib. Excellent for formalized mathematics."
        },
        ProverKind::Isabelle => {
            "Generic proof assistant supporting multiple logics (mainly HOL).\n  \
             Powerful automation through Sledgehammer. Large Archive of Formal Proofs."
        },
        ProverKind::Z3 => {
            "High-performance SMT (Satisfiability Modulo Theories) solver.\n  \
             Excellent for automated reasoning in program verification."
        },
        ProverKind::CVC5 => {
            "Automatic SMT solver for first-order logic with theories.\n  \
             Strong support for quantifiers, datatypes, and strings."
        },
        ProverKind::Metamath => {
            "Ultra-minimal proof verification system with plain-text proofs.\n  \
             EASIEST to integrate (2/5 complexity). Large database of formalized mathematics."
        },
        ProverKind::HOLLight => {
            "Simple, elegant HOL (Higher-Order Logic) proof assistant in OCaml.\n  \
             Part of the 'Big Six' theorem provers. Strong mathematical foundations."
        },
        ProverKind::Mizar => {
            "Proof assistant with natural-language-like proof style.\n  \
             Large Mathematical Library. Readable proof documents."
        },
        ProverKind::PVS => {
            "Specification and verification system for safety-critical systems.\n  \
             Strong support for dependent types and predicate subtyping."
        },
        ProverKind::ACL2 => {
            "Computational Logic for Applicative Common Lisp.\n  \
             Industrial-strength theorem prover for software/hardware verification."
        },
        ProverKind::HOL4 => {
            "Interactive theorem prover in the HOL family.\n  \
             Used extensively in hardware verification. ML-based tactic language."
        },
        ProverKind::Idris2 => {
            "Dependently typed functional language with quantitative types.\n  \
             First-class type-level computation, elaborator reflection, linear types."
        },
        ProverKind::Vampire => {
            "First-order automated theorem prover. Multiple CASC winner.\n  \
             Superposition calculus with excellent performance on CASC benchmarks."
        },
        ProverKind::EProver => {
            "Highly optimized first-order theorem prover for clausal logic.\n  \
             CASC winner. Auto mode with sophisticated strategy selection."
        },
        ProverKind::SPASS => {
            "First-order theorem prover with sorted logic support.\n  \
             DFG format input. Superposition calculus with sort handling."
        },
        ProverKind::AltErgo => {
            "SMT solver with polymorphic first-order logic.\n  \
             Designed for program verification (Why3, Frama-C integration)."
        },
        ProverKind::FStar => {
            "F* dependent types with effects. Project Everest/HACL* verified crypto."
        },
        ProverKind::Dafny => "Auto-active verifier. Pre/postconditions verified via Boogie and Z3.",
        ProverKind::Why3 => {
            "Multi-prover orchestration. Dispatches to Z3, CVC5, Alt-Ergo in parallel."
        },
        ProverKind::TLAPS => "TLA+ Proof System. Verifies distributed system properties.",
        ProverKind::Twelf => "Logical framework (LF). Metatheory verification for type systems.",
        ProverKind::Nuprl => "Constructive type theory. Large library of formalized mathematics.",
        ProverKind::Minlog => "Minimal logic with certified program extraction from proofs.",
        ProverKind::Imandra => "ML-based reasoning for industrial verification.",
        ProverKind::GLPK => "GNU Linear Programming Kit. LP/MIP constraint solving.",
        ProverKind::SCIP => "Mixed-integer nonlinear programming solver.",
        ProverKind::MiniZinc => "Constraint modelling language with multiple backend solvers.",
        ProverKind::Chuffed => "Lazy clause generation CP solver with SAT-style learning.",
        ProverKind::ORTools => "Google OR-Tools. CP-SAT, routing, linear/integer programming.",
        ProverKind::TypedWasm => {
            "TypedWasm oracle. 10-level type safety validation for .twasm programs."
        },
        ProverKind::SPIN => "SPIN model checker for Promela concurrent system specifications.",
        ProverKind::CBMC => "C Bounded Model Checker. Verifies C programs via bounded unwinding.",
        ProverKind::CaDiCaL => {
            "State-of-the-art CDCL SAT solver. DIMACS CNF input.\n  \
             Multiple SAT Competition winner. Default SAT backend for ECHIDNA."
        },
        ProverKind::Kissat => {
            "Fast, highly-optimised CDCL SAT solver. DIMACS CNF input.\n  \
             SAT Competition winner. Designed for raw solving speed."
        },
        ProverKind::MiniSat => {
            "Classic DPLL/CDCL SAT solver. DIMACS CNF input. Reference implementation."
        },
        ProverKind::NuSMV => {
            "NuSMV/nuXmv symbolic model checker for CTL/LTL verification of finite state systems."
        },
        ProverKind::TLC => {
            "TLC model checker for exhaustive state exploration of TLA+ specifications."
        },
        ProverKind::Alloy => "Alloy relational model finder using SAT-based bounded analysis.",
        ProverKind::Prism => "PRISM probabilistic model checker for DTMCs, CTMCs, MDPs, and PTAs.",
        ProverKind::UPPAAL => {
            "UPPAAL timed automata model checker for real-time system verification."
        },
        ProverKind::FramaC => "Frama-C WP deductive verifier for ACSL-annotated C programs.",
        ProverKind::SeaHorn => "SeaHorn verification framework for LLVM-based safety checking.",
        ProverKind::Viper => "Viper permission-based program verifier with separation logic.",
        ProverKind::Tamarin => {
            "Tamarin security protocol prover using multiset rewriting in the Dolev-Yao model."
        },
        ProverKind::ProVerif => {
            "ProVerif automatic cryptographic protocol verifier in the Dolev-Yao model."
        },
        ProverKind::KeY => {
            "KeY deductive Java verifier using JavaDL (dynamic logic) with JML contracts."
        },
        ProverKind::DReal => {
            "dReal delta-complete SMT solver for nonlinear real arithmetic over the reals."
        },
        ProverKind::ABC => {
            "ABC sequential logic synthesis and verification system for hardware circuits."
        },
        // HP ecosystem type-disciplines (TypeDiscipline transition, 2026-04-17).
        // A single-line fallback for the forty discipline views; per-discipline
        // descriptions are a phase-2 followup tracked in AI-WORK-todo.md.
        k if k.is_hp_ecosystem() => {
            "HP ecosystem type-discipline view. Dispatches through typell / \n  \
             katagoria / tropical-resource-typing. See disciplines/ for the \n  \
             40-variant taxonomy (linear, affine, phantom, modal, etc.)."
        },
        _ => "No description available for this prover.",
    };
    formatter.info(&format!("  {}", description))?;
    formatter.info("")?;

    formatter.section("File Extensions")?;
    let extension = match prover {
        ProverKind::Agda => ".agda",
        ProverKind::Coq => ".v",
        ProverKind::Lean => ".lean",
        ProverKind::Isabelle => ".thy",
        ProverKind::Z3 | ProverKind::CVC5 => ".smt2",
        ProverKind::Metamath => ".mm",
        ProverKind::HOLLight => ".ml",
        ProverKind::Mizar => ".miz",
        ProverKind::PVS => ".pvs",
        ProverKind::ACL2 => ".lisp",
        ProverKind::HOL4 => ".sml",
        ProverKind::Idris2 => ".idr",
        ProverKind::Vampire => ".p / .tptp",
        ProverKind::EProver => ".p / .tptp",
        ProverKind::SPASS => ".dfg",
        ProverKind::AltErgo => ".ae / .why",
        ProverKind::FStar => ".fst / .fsti",
        ProverKind::Dafny => ".dfy",
        ProverKind::Why3 => ".why / .mlw",
        ProverKind::TLAPS => ".tla",
        ProverKind::Twelf => ".elf",
        ProverKind::Nuprl => ".nuprl",
        ProverKind::Minlog => ".minlog",
        ProverKind::Imandra => ".iml",
        ProverKind::GLPK => ".lp / .mps",
        ProverKind::SCIP => ".pip / .zpl",
        ProverKind::MiniZinc => ".mzn / .dzn",
        ProverKind::Chuffed => ".fzn",
        ProverKind::ORTools => ".or / .proto",
        ProverKind::TypedWasm => ".twasm",
        ProverKind::SPIN => ".pml",
        ProverKind::CBMC => ".c",
        ProverKind::CaDiCaL => ".cnf",
        ProverKind::Kissat => ".cnf",
        ProverKind::MiniSat => ".cnf",
        ProverKind::NuSMV => ".smv",
        ProverKind::TLC => ".tla",
        ProverKind::Alloy => ".als",
        ProverKind::Prism => ".pm / .prism",
        ProverKind::UPPAAL => ".xml",
        ProverKind::FramaC => ".c (ACSL-annotated)",
        ProverKind::SeaHorn => ".bc / .ll (LLVM IR)",
        ProverKind::Viper => ".vpr",
        ProverKind::Tamarin => ".spthy",
        ProverKind::ProVerif => ".pv",
        ProverKind::KeY => ".java (JML-annotated)",
        ProverKind::DReal => ".smt2 (QF_NRA/NRA)",
        ProverKind::ABC => ".blif / .aig",
        // HP ecosystem: discipline-tagged source lives in typell; no fixed
        // extension. See HPEcosystemBackend for the actual dispatch.
        k if k.is_hp_ecosystem() => "typell discipline source (.tll / #discipline header)",
        _ => "unknown",
    };
    formatter.info(&format!("  {}", extension))?;
    formatter.info("")?;

    formatter.section("Features")?;
    formatter.info("  ✓ Neural premise selection")?;
    formatter.info("  ✓ Aspect tagging")?;
    formatter.info("  ✓ OpenCyc integration")?;
    formatter.info("  ✓ Tactic suggestion")?;
    formatter.info("")?;

    // Try to get version if prover is installed
    let config = ProverConfig::default();
    if let Ok(prover_backend) = echidna::provers::ProverFactory::create(prover, config) {
        formatter.section("Installation")?;

        // Spawn async runtime to check version
        let version_check = tokio::task::spawn(async move { prover_backend.version().await });

        if let Ok(Ok(version)) = futures::executor::block_on(version_check) {
            formatter.success(&format!("  ✓ Installed: {}", version))?;
        } else {
            formatter.warning("  ✗ Not detected (may not be installed or not in PATH)")?;
        }
    }

    Ok(())
}

/// Detect prover from file extension or use specified prover
fn detect_prover(prover_kind: Option<ProverKind>, file: &std::path::Path) -> Result<ProverKind> {
    if let Some(kind) = prover_kind {
        return Ok(kind);
    }

    echidna::provers::ProverFactory::detect_from_file(file).ok_or_else(|| {
        anyhow::anyhow!(
            "Could not detect prover from file extension: {}. Please specify with --prover",
            file.display()
        )
    })
}

/// Create prover configuration
fn create_config(
    kind: ProverKind,
    timeout: u64,
    neural: bool,
    executable: Option<PathBuf>,
    library: Vec<PathBuf>,
    project_root: Option<PathBuf>,
    sandbox: &str,
) -> Result<ProverConfig> {
    let sandbox_mode: echidna::provers::SandboxMode = sandbox
        .parse()
        .map_err(|e: String| anyhow::anyhow!(e))?;

    let config = ProverConfig {
        timeout,
        neural_enabled: neural,
        executable: executable.unwrap_or_else(|| get_default_executable(kind)),
        library_paths: if library.is_empty() {
            ProverConfig::default().library_paths
        } else {
            library
        },
        project_root,
        sandbox: sandbox_mode,
        ..ProverConfig::default()
    };

    Ok(config)
}

/// Get default executable path for a prover
fn get_default_executable(kind: ProverKind) -> PathBuf {
    match kind {
        ProverKind::Agda => PathBuf::from("agda"),
        ProverKind::Coq => PathBuf::from("coqtop"),
        ProverKind::Lean => PathBuf::from("lean"),
        ProverKind::Isabelle => PathBuf::from("isabelle"),
        ProverKind::Z3 => PathBuf::from("z3"),
        ProverKind::CVC5 => PathBuf::from("cvc5"),
        ProverKind::Metamath => PathBuf::from("metamath"),
        ProverKind::HOLLight => PathBuf::from("ocaml"),
        ProverKind::Mizar => PathBuf::from("verifier"),
        ProverKind::PVS => PathBuf::from("pvs"),
        ProverKind::ACL2 => PathBuf::from("acl2"),
        ProverKind::HOL4 => PathBuf::from("hol"),
        ProverKind::Idris2 => PathBuf::from("idris2"),
        ProverKind::Vampire => PathBuf::from("vampire"),
        ProverKind::EProver => PathBuf::from("eprover"),
        ProverKind::SPASS => PathBuf::from("SPASS"),
        ProverKind::AltErgo => PathBuf::from("alt-ergo"),
        ProverKind::FStar => PathBuf::from("fstar.exe"),
        ProverKind::Dafny => PathBuf::from("dafny"),
        ProverKind::Why3 => PathBuf::from("why3"),
        ProverKind::TLAPS => PathBuf::from("tlapm"),
        ProverKind::Twelf => PathBuf::from("twelf-server"),
        ProverKind::Nuprl => PathBuf::from("nuprl"),
        ProverKind::Minlog => PathBuf::from("minlog"),
        ProverKind::Imandra => PathBuf::from("imandra"),
        ProverKind::GLPK => PathBuf::from("glpsol"),
        ProverKind::SCIP => PathBuf::from("scip"),
        ProverKind::MiniZinc => PathBuf::from("minizinc"),
        ProverKind::Chuffed => PathBuf::from("fzn-chuffed"),
        ProverKind::ORTools => PathBuf::from("ortools_solve"),
        ProverKind::TypedWasm => PathBuf::from("idris2"),
        ProverKind::SPIN => PathBuf::from("spin"),
        ProverKind::CBMC => PathBuf::from("cbmc"),
        ProverKind::CaDiCaL => PathBuf::from("cadical"),
        ProverKind::Kissat => PathBuf::from("kissat"),
        ProverKind::MiniSat => PathBuf::from("minisat"),
        ProverKind::NuSMV => PathBuf::from("nuXmv"),
        ProverKind::TLC => PathBuf::from("tlc2.TLC"),
        ProverKind::Alloy => PathBuf::from("alloy"),
        ProverKind::Prism => PathBuf::from("prism"),
        ProverKind::UPPAAL => PathBuf::from("verifyta"),
        ProverKind::FramaC => PathBuf::from("frama-c"),
        ProverKind::SeaHorn => PathBuf::from("seahorn"),
        ProverKind::Viper => PathBuf::from("viper"),
        ProverKind::Tamarin => PathBuf::from("tamarin-prover"),
        ProverKind::ProVerif => PathBuf::from("proverif"),
        ProverKind::KeY => PathBuf::from("key"),
        ProverKind::DReal => PathBuf::from("dreal"),
        ProverKind::ABC => PathBuf::from("abc"),
        // HP ecosystem: route through the TypeLL kernel CLI, with two named
        // exceptions (katagoria, tropical-type-check). Mirrors provers/mod.rs
        // default_executable() — source of truth is that function.
        kind if kind.is_hp_ecosystem() => PathBuf::from(kind.default_executable()),
        _ => PathBuf::from(kind.default_executable()),
    }
}

/// Create a progress bar with standard styling
fn create_progress_bar(message: &str) -> ProgressBar {
    let pb = ProgressBar::new_spinner();
    pb.set_style(
        ProgressStyle::default_spinner()
            .template("{spinner:.green} {msg}")
            .expect("Failed to set progress bar template"),
    );
    pb.set_message(message.to_string());
    pb.enable_steady_tick(std::time::Duration::from_millis(100));
    pb
}

/// Diagnostics command - interactive health monitoring REPL
async fn diagnostics_command() -> Result<()> {
    info!("Starting diagnostics REPL for health monitoring");
    let dispatcher = Arc::new(ProverDispatcher::new());
    let health = dispatcher.health_status();
    let mut repl = DiagnosticsREPL::new();
    repl.run(&health).await;
    Ok(())
}

/// Corpus command - ingest, query, or summarise a project corpus.
///
/// First adapter is `agda`, targeted at echo-types' Buchholz / Brouwer
/// proof tree. Build the index once with `corpus ingest --root …`,
/// then query it without re-walking the source. The index is plain
/// JSON at `data/corpus/<basename>.json` so other tools (suggest, the
/// upcoming SA design search) can consume it directly.
fn corpus_command(op: CorpusOp, formatter: &OutputFormatter) -> Result<()> {
    use echidna::corpus::{self, Corpus};

    let default_index = |root_basename: &str| -> PathBuf {
        PathBuf::from("data/corpus").join(format!("{}.json", root_basename))
    };

    match op {
        CorpusOp::Ingest { root, adapter, out } => {
            let root = root.canonicalize().unwrap_or(root);
            let basename = root
                .file_name()
                .map(|s| s.to_string_lossy().into_owned())
                .unwrap_or_else(|| "project".to_string());
            let out = out.unwrap_or_else(|| default_index(&basename));

            let corpus = match adapter.as_str() {
                "agda" => corpus::agda::ingest(&root)
                    .with_context(|| format!("agda ingest of {}", root.display()))?,
                other => {
                    return Err(anyhow::anyhow!(
                        "Unknown corpus adapter '{}' (supported: agda)",
                        other
                    ))
                }
            };
            corpus.save_json(&out)?;
            let stats = corpus.stats();
            formatter.info(&format!(
                "ingested {} module(s), {} entry/-ies ({} fn, {} data, {} record, {} postulate); {} entry/-ies have hazards; index: {}",
                stats.modules,
                stats.entries,
                stats.functions,
                stats.data,
                stats.records,
                stats.postulates,
                stats.with_hazards,
                out.display()
            ))?;
        }
        CorpusOp::Query {
            pattern,
            index,
            deps,
        } => {
            let path = match index {
                Some(p) => p,
                None => {
                    let basename = std::env::current_dir()?
                        .file_name()
                        .map(|s| s.to_string_lossy().into_owned())
                        .unwrap_or_else(|| "project".to_string());
                    default_index(&basename)
                }
            };
            let corpus = Corpus::load_json(&path)
                .with_context(|| format!("load corpus index {}", path.display()))?;
            let hits = corpus.find(&pattern);
            if hits.is_empty() {
                formatter.info(&format!("no matches for '{}'", pattern))?;
                return Ok(());
            }
            for entry in &hits {
                let module = corpus
                    .modules
                    .get(entry.module_idx)
                    .map(|m| m.name.as_str())
                    .unwrap_or("?");
                println!(
                    "{}  [{:?}] {}:{}",
                    entry.qualified,
                    entry.kind,
                    module,
                    entry.line
                );
                println!("  : {}", entry.statement);
                if entry.axiom_usage.any() {
                    println!("  ⚠ hazards: {:?}", entry.axiom_usage);
                }
                if !entry.dependencies.is_empty() {
                    let mut deps_list = entry.dependencies.clone();
                    deps_list.sort();
                    println!("  deps ({}): {}", deps_list.len(), deps_list.join(", "));
                }
            }
            if deps && hits.len() == 1 {
                let closure = corpus.closure(&hits[0].qualified);
                println!("\ntransitive closure ({} entries):", closure.len());
                let mut names: Vec<&str> =
                    closure.iter().map(|e| e.qualified.as_str()).collect();
                names.sort();
                for n in names {
                    println!("  {}", n);
                }
            }
        }
        CorpusOp::Stats { index } => {
            let path = match index {
                Some(p) => p,
                None => {
                    let basename = std::env::current_dir()?
                        .file_name()
                        .map(|s| s.to_string_lossy().into_owned())
                        .unwrap_or_else(|| "project".to_string());
                    default_index(&basename)
                }
            };
            let corpus = Corpus::load_json(&path)
                .with_context(|| format!("load corpus index {}", path.display()))?;
            let stats = corpus.stats();
            println!(
                "modules:    {}\nentries:    {}\n  functions:  {}\n  data:       {}\n  records:    {}\n  postulates: {}\nwith hazards: {}\nwith deps:    {}",
                stats.modules,
                stats.entries,
                stats.functions,
                stats.data,
                stats.records,
                stats.postulates,
                stats.with_hazards,
                stats.with_deps
            );
        }
    }

    Ok(())
}

/// Design-search command — simulated annealing over candidate
/// axiomatisations, single-chain or parallel swarm. The first
/// concrete problem is `brouwer-leq`, targeting echo-types' Phase 1.3
/// `_≤_` redesign.
async fn design_command(op: DesignOp, formatter: &OutputFormatter) -> Result<()> {
    use echidna::agent::swarm::{run_swarm, SwarmConfig};
    use echidna::learning::design_search::{anneal, brouwer, AnnealConfig, DesignProblem};
    use std::sync::Arc;

    match op {
        DesignOp::Search {
            problem,
            iterations,
            restarts,
            temp,
            cooling,
            seed,
            top,
        } => {
            let cfg = AnnealConfig {
                max_iterations: iterations,
                initial_temp: temp,
                cooling,
                seed,
                restarts,
            };

            match problem.as_str() {
                "brouwer-leq" => {
                    let p = brouwer::BrouwerLeqProblem::default();
                    let result = anneal(&p, &cfg);
                    formatter.info(&format!(
                        "annealer: {} steps, {} accepted ({:.1}%); best energy {:?}",
                        result.steps,
                        result.accepted,
                        100.0 * result.accepted as f64 / result.steps.max(1) as f64,
                        result.best_energy
                    ))?;
                    println!(
                        "\nbest design (energy = {:?}):\n  {}\n",
                        result.best_energy,
                        p.describe(&result.best)
                    );
                    println!("top {} distinct candidates:", top.min(result.topk.len()));
                    for (i, (state, e)) in result.topk.iter().take(top).enumerate() {
                        println!(
                            "  {:2}. energy {:?}  {}",
                            i + 1,
                            e,
                            p.describe(state)
                        );
                    }
                    println!(
                        "\nlegend: energy = [mono-blockers, K-hazards, ctor-count, style-pref]"
                    );
                    println!(
                        "        style-pref: 0 = recursive, 1 = data (recursive preferred when tied)"
                    );
                }
                other => {
                    return Err(anyhow::anyhow!(
                        "Unknown design problem '{}' (available: brouwer-leq)",
                        other
                    ))
                }
            }
        }

        DesignOp::Swarm {
            problem,
            agents,
            iterations,
            temp,
            cooling,
            seed,
            broadcast_every,
            adopt_threshold,
        } => {
            let anneal_cfg = AnnealConfig {
                max_iterations: iterations,
                initial_temp: temp,
                cooling,
                seed,
                restarts: 1, // each swarm agent is its own "restart"
            };
            let swarm_cfg = SwarmConfig {
                agents,
                anneal: anneal_cfg,
                broadcast_every,
                adopt_threshold,
            };

            match problem.as_str() {
                "brouwer-leq" => {
                    let p = Arc::new(brouwer::BrouwerLeqProblem::default());
                    let p_describe = brouwer::BrouwerLeqProblem::default();
                    let result = run_swarm(p, swarm_cfg).await;
                    formatter.info(&format!(
                        "swarm: {} agents, {} adoptions; best energy {:?}",
                        result.per_agent.len(),
                        result.adoptions,
                        result.best_energy
                    ))?;
                    println!(
                        "\nbest design (energy = {:?}):\n  {}\n",
                        result.best_energy,
                        p_describe.describe(&result.best)
                    );
                    println!("per-agent reports:");
                    for r in &result.per_agent {
                        println!(
                            "  agent {:2} (seed {:#x}): {} steps, {} accepted, {} adoptions; best {:?}",
                            r.agent_id,
                            r.seed,
                            r.steps,
                            r.accepted,
                            r.adopted_count,
                            r.local_best_energy,
                        );
                    }
                }
                other => {
                    return Err(anyhow::anyhow!(
                        "Unknown design problem '{}' (available: brouwer-leq)",
                        other
                    ))
                }
            }
        }
    }
    Ok(())
}

// We need to add futures crate for the executor
