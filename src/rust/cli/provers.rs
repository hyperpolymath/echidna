// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! `echidna` CLI: provers. Moved verbatim from main.rs (hotspot split).

use crate::output::OutputFormatter;
use anyhow::Result;
use echidna::{ProverConfig, ProverKind};

/// List provers command
pub(crate) fn list_provers_command(detailed: bool, formatter: &OutputFormatter) -> Result<()> {
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
pub(crate) fn info_command(prover: ProverKind, formatter: &OutputFormatter) -> Result<()> {
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
