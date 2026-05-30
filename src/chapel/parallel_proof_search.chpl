// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// ECHIDNA Chapel Metalayer — Parallel Proof Search
//
// Dispatches theorem proving goals to all 30 prover backends concurrently
// using Chapel's coforall for true data parallelism. Each prover is invoked
// as a subprocess with a timeout; the first successful proof wins.

use Time;
use IO;
use FileSystem;
use Subprocess;
use Path;
use List;

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

config const numProvers = 30;
config const verbose = true;
config const defaultTimeout = 300; // seconds

// ---------------------------------------------------------------------------
// Prover registry — all 30 ECHIDNA backends
// ---------------------------------------------------------------------------

// Prover category tags for reporting
enum ProverCategory {
    InteractiveAssistant,
    SmtSolver,
    FirstOrderAtp,
    DeclarativeProver,
    AutoActive,
    ConstraintSolver
}

record ProverInfo {
    var id: int;
    var name: string;
    var executable: string;
    var category: ProverCategory;
    var fileExt: string;       // file extension for temp input files
    var argTemplate: string;   // how to pass the input file (%FILE% placeholder)
}

// Build the full 30-prover registry
proc buildProverRegistry(): [0..29] ProverInfo {
    var provers: [0..29] ProverInfo;

    // Tier 1: Interactive proof assistants (10)
    provers[0]  = new ProverInfo(0,  "Agda",      "agda",          ProverCategory.InteractiveAssistant, "agda",  "--safe %FILE%");
    provers[1]  = new ProverInfo(1,  "Coq",       "coqc",          ProverCategory.InteractiveAssistant, "v",     "%FILE%");
    provers[2]  = new ProverInfo(2,  "Lean",      "lean",          ProverCategory.InteractiveAssistant, "lean",  "%FILE%");
    provers[3]  = new ProverInfo(3,  "Isabelle",  "isabelle",      ProverCategory.InteractiveAssistant, "thy",   "process %FILE%");
    provers[4]  = new ProverInfo(4,  "Idris2",    "idris2",        ProverCategory.InteractiveAssistant, "idr",   "--check %FILE%");
    provers[5]  = new ProverInfo(5,  "FStar",     "fstar.exe",     ProverCategory.InteractiveAssistant, "fst",   "%FILE%");
    provers[6]  = new ProverInfo(6,  "HOL4",      "hol",           ProverCategory.InteractiveAssistant, "sml",   "< %FILE%");
    provers[7]  = new ProverInfo(7,  "HOLLight",  "ocaml",         ProverCategory.InteractiveAssistant, "ml",    "%FILE%");
    provers[8]  = new ProverInfo(8,  "Nuprl",     "nuprl",         ProverCategory.InteractiveAssistant, "nuprl", "%FILE%");
    provers[9]  = new ProverInfo(9,  "Minlog",    "minlog",        ProverCategory.InteractiveAssistant, "minlog","%FILE%");

    // Tier 2: SMT solvers (3)
    provers[10] = new ProverInfo(10, "Z3",        "z3",            ProverCategory.SmtSolver,            "smt2",  "%FILE%");
    provers[11] = new ProverInfo(11, "CVC5",      "cvc5",          ProverCategory.SmtSolver,            "smt2",  "--lang smt2 %FILE%");
    provers[12] = new ProverInfo(12, "AltErgo",   "alt-ergo",      ProverCategory.SmtSolver,            "ae",    "%FILE%");

    // Tier 3: First-order ATPs (3)
    provers[13] = new ProverInfo(13, "Vampire",   "vampire",       ProverCategory.FirstOrderAtp,        "p",     "--mode casc %FILE%");
    provers[14] = new ProverInfo(14, "EProver",   "eprover",       ProverCategory.FirstOrderAtp,        "p",     "--auto %FILE%");
    provers[15] = new ProverInfo(15, "SPASS",     "SPASS",         ProverCategory.FirstOrderAtp,        "dfg",   "%FILE%");

    // Tier 4: Declarative provers (7)
    provers[16] = new ProverInfo(16, "Metamath",  "metamath",      ProverCategory.DeclarativeProver,    "mm",    "read %FILE% verify proof *");
    provers[17] = new ProverInfo(17, "Mizar",     "mizf",          ProverCategory.DeclarativeProver,    "miz",   "%FILE%");
    provers[18] = new ProverInfo(18, "PVS",       "pvs",           ProverCategory.DeclarativeProver,    "pvs",   "-batch %FILE%");
    provers[19] = new ProverInfo(19, "ACL2",      "acl2",          ProverCategory.DeclarativeProver,    "lisp",  "< %FILE%");
    provers[20] = new ProverInfo(20, "TLAPS",     "tlapm",         ProverCategory.DeclarativeProver,    "tla",   "%FILE%");
    provers[21] = new ProverInfo(21, "Twelf",     "twelf-server",  ProverCategory.DeclarativeProver,    "elf",   "%FILE%");
    provers[22] = new ProverInfo(22, "Imandra",   "imandra",       ProverCategory.DeclarativeProver,    "iml",   "%FILE%");

    // Tier 5: Auto-active verifiers (2)
    provers[23] = new ProverInfo(23, "Dafny",     "dafny",         ProverCategory.AutoActive,           "dfy",   "verify %FILE%");
    provers[24] = new ProverInfo(24, "Why3",      "why3",          ProverCategory.AutoActive,           "mlw",   "prove %FILE%");

    // Tier 6: Constraint solvers (5)
    provers[25] = new ProverInfo(25, "GLPK",      "glpsol",        ProverCategory.ConstraintSolver,     "lp",    "--lp %FILE%");
    provers[26] = new ProverInfo(26, "SCIP",      "scip",          ProverCategory.ConstraintSolver,     "pip",   "-f %FILE%");
    provers[27] = new ProverInfo(27, "MiniZinc",  "minizinc",      ProverCategory.ConstraintSolver,     "mzn",   "%FILE%");
    provers[28] = new ProverInfo(28, "Chuffed",   "fzn-chuffed",   ProverCategory.ConstraintSolver,     "fzn",   "%FILE%");
    provers[29] = new ProverInfo(29, "ORTools",   "ortools_solve", ProverCategory.ConstraintSolver,     "proto", "%FILE%");

    return provers;
}

// ---------------------------------------------------------------------------
// Proof result
// ---------------------------------------------------------------------------

record ProofResult {
    var success: bool;
    var prover: string;
    var proverId: int;
    var time: real;
    var exitCode: int;
    var output: string;
    var category: ProverCategory;
}

// ---------------------------------------------------------------------------
// Prover availability check
// ---------------------------------------------------------------------------

// Check if a prover executable exists on PATH. `stdout = pipeStyle.pipe`
// stops `which` from leaking the resolved path into the parent's stdout,
// which would otherwise mangle structured output (CSV, JSON) from callers
// like `bench_mrr`.
proc isProverAvailable(info: ProverInfo): bool {
    try {
        var whichProc = spawn(["which", info.executable],
                              stdout = pipeStyle.pipe,
                              stderr = pipeStyle.pipe);
        whichProc.wait();
        return whichProc.exitCode == 0;
    } catch {
        return false;
    }
}

// ---------------------------------------------------------------------------
// Real prover invocation via subprocess
// ---------------------------------------------------------------------------

// Write goal content to a temporary file and invoke the prover
proc tryProver(info: ProverInfo, goal: string, timeout: int = defaultTimeout): ProofResult {
    var timer = new stopwatch();
    timer.start();

    // Check availability first
    if !isProverAvailable(info) {
        timer.stop();
        return new ProofResult(
            success = false,
            prover = info.name,
            proverId = info.id,
            time = timer.elapsed(),
            exitCode = -1,
            output = "Prover not available on PATH",
            category = info.category
        );
    }

    // Write goal to temp file
    const tmpDir = "/tmp/echidna-chapel";
    if !exists(tmpDir) then mkdir(tmpDir);

    const tmpFile = tmpDir + "/goal_" + info.name:string + "_" + here.id:string + "." + info.fileExt;

    try {
        var f = open(tmpFile, ioMode.cw);
        var w = f.writer(locking=false);
        w.write(goal);
        w.close();
        f.close();
    } catch e {
        timer.stop();
        return new ProofResult(
            success = false,
            prover = info.name,
            proverId = info.id,
            time = timer.elapsed(),
            exitCode = -2,
            output = "Failed to write temp file: " + e.message(),
            category = info.category
        );
    }

    // Build argument vector. First entry is the executable; the rest come
    // from splitting `argTemplate` after `%FILE%` substitution. `list(string)`
    // is used rather than a fixed array because the argument count is
    // template-driven and varies per prover.
    var cmdStr = info.argTemplate.replace("%FILE%", tmpFile);
    var argList: list(string);
    argList.pushBack(info.executable);
    for part in cmdStr.split(" ") {
        if part.size > 0 then argList.pushBack(part);
    }
    var args = argList.toArray();

    // Invoke prover subprocess. `stdout = pipeStyle.pipe` is required so
    // the parent can read the prover's output once it terminates; without
    // it the subprocess inherits the parent's stdout and `subproc.stdout`
    // is not a readable channel.
    try {
        var subproc = spawn(args, stdout = pipeStyle.pipe);

        // Bounded poll-wait: poll every 100 ms, capped at `timeout` seconds.
        // The previous implementation used `!proc.running` which is true
        // before the child has begun and after it has exited, so it was
        // both racy at startup and stopped polling once running latched.
        var elapsed: real = 0.0;
        const pollInterval: real = 0.1;
        while subproc.running && elapsed < timeout:real {
            sleep(pollInterval);
            elapsed += pollInterval;
            subproc.poll();
        }

        if subproc.running {
            // Timeout reached while child still alive — SIGKILL it.
            // 2.x renamed `send_signal` → `sendPosixSignal`.
            subproc.sendPosixSignal(9);
            subproc.wait();
            timer.stop();
            try { remove(tmpFile); } catch { }
            return new ProofResult(
                success = false,
                prover = info.name,
                proverId = info.id,
                time = timer.elapsed(),
                exitCode = -3,
                output = "Timeout after " + timeout:string + "s",
                category = info.category
            );
        }

        subproc.wait();
        timer.stop();

        var stdoutText = "";
        try {
            // 2.x: `subproc.stdout` is itself a `fileReader` when the
            // subprocess was spawned with `stdout = pipeStyle.pipe`, so
            // we read directly. The old `.reader(locking=false)` indirection
            // belonged to the 1.x `file`-based API.
            stdoutText = subproc.stdout.readAll(string);
        } catch { }

        try { remove(tmpFile); } catch { }

        return new ProofResult(
            success = subproc.exitCode == 0,
            prover = info.name,
            proverId = info.id,
            time = timer.elapsed(),
            exitCode = subproc.exitCode,
            output = stdoutText,
            category = info.category
        );
    } catch e {
        timer.stop();
        try { remove(tmpFile); } catch { }
        return new ProofResult(
            success = false,
            prover = info.name,
            proverId = info.id,
            time = timer.elapsed(),
            exitCode = -4,
            output = "Subprocess error: " + e.message(),
            category = info.category
        );
    }
}

// ---------------------------------------------------------------------------
// Search strategies
// ---------------------------------------------------------------------------

// Sequential proof search (baseline) — tries provers one by one
proc sequentialProofSearch(goal: string, provers: [] ProverInfo,
                           timeout: int = defaultTimeout): ProofResult {
    if verbose then
        writeln("Sequential search: trying ", provers.size, " provers one by one...");

    var totalTimer = new stopwatch();
    totalTimer.start();

    for prover in provers {
        if verbose then
            write("  Trying ", prover.name, "...");

        var result = tryProver(prover, goal, timeout);

        if verbose then
            writeln(if result.success then " ✓ SUCCESS (" + result.time:string + "s)"
                   else " ✗ " + result.output);

        if result.success {
            totalTimer.stop();
            if verbose then
                writeln("\nFound proof via ", result.prover, " in ",
                       totalTimer.elapsed(), " seconds");
            return result;
        }
    }

    totalTimer.stop();
    if verbose then
        writeln("\nNo proof found after ", totalTimer.elapsed(), " seconds");

    return new ProofResult(
        success = false, prover = "", proverId = -1,
        time = totalTimer.elapsed(), exitCode = -1,
        output = "All provers exhausted",
        category = ProverCategory.InteractiveAssistant
    );
}

// Parallel proof search — tries ALL provers concurrently via coforall
proc parallelProofSearch(goal: string, provers: [] ProverInfo,
                          timeout: int = defaultTimeout): ProofResult {
    if verbose then
        writeln("Parallel search: trying all ", provers.size,
               " provers concurrently...");

    var totalTimer = new stopwatch();
    totalTimer.start();

    // Results array — one per prover
    var results: [provers.domain] ProofResult;

    // Launch all provers in parallel
    coforall (prover, i) in zip(provers, provers.domain) {
        results[i] = tryProver(prover, goal, timeout);

        if verbose && results[i].success {
            writef("  ✓ %s succeeded in %.2dr seconds (exit %i)\n",
                   prover.name, results[i].time, results[i].exitCode);
        }
    }

    totalTimer.stop();

    // Find best successful result (fastest proof time)
    var bestIdx = -1;
    var bestTime = 1e18;

    for i in provers.domain {
        if results[i].success && results[i].time < bestTime {
            bestIdx = i;
            bestTime = results[i].time;
        }
    }

    if verbose {
        var successCount = + reduce [r in results] if r.success then 1 else 0;
        var availCount = + reduce [r in results] if r.exitCode != -1 then 1 else 0;
        writeln("\nParallel search completed in ",
               totalTimer.elapsed(), " seconds");
        writeln("  Available provers: ", availCount, "/", provers.size);
        writeln("  Successful proofs: ", successCount, "/", availCount);
    }

    if bestIdx >= 0 {
        return results[bestIdx];
    } else {
        return new ProofResult(
            success = false, prover = "", proverId = -1,
            time = totalTimer.elapsed(), exitCode = -1,
            output = "All provers exhausted",
            category = ProverCategory.InteractiveAssistant
        );
    }
}

// L2.2 speculative search — race all provers, return the first success.
//
// Semantics vs `parallelProofSearch` (best-of):
//   - parallelProofSearch waits for ALL tasks then picks the fastest
//     success. Wall time is bounded by the slowest prover.
//   - parallelProofSearchSpeculative records the first-completing
//     success via an atomic CAS and returns it. Wall time is bounded
//     by the fastest successful prover plus whatever in-flight tasks
//     have already begun (no mid-flight preemption in Wave 1).
//
// Wave 1 scope deliberately stops short of the "kill in-flight losers"
// step. Once a prover has been spawned, `tryProver` runs it to its own
// per-prover timeout — coforall doesn't know how to cancel a child task
// that's blocked on subprocess I/O. L2.3 introduces a cancel token
// threaded through `tryProver` so the children can SIGKILL their own
// subprocesses when they observe a winner; that's a separate PR.
//
// Cancellation-safety today: every losing task is run to its natural
// end. The result table records all outcomes; only the winning index
// (the first successful CAS) is returned. No prover's exit can poison
// the join because the atomic CAS is monotone — the first winner wins.
proc parallelProofSearchSpeculative(goal: string, provers: [] ProverInfo,
                                    timeout: int = defaultTimeout): ProofResult {
    if verbose then
        writeln("Speculative search: ", provers.size,
                " provers racing, first-success-wins");

    var totalTimer = new stopwatch();
    totalTimer.start();

    var results: [provers.domain] ProofResult;
    var winnerIdx: atomic int;
    winnerIdx.write(-1);

    coforall (prover, i) in zip(provers, provers.domain) {
        results[i] = tryProver(prover, goal, timeout);

        if results[i].success {
            // Monotone first-wins CAS: only the first successful
            // worker flips the atomic from -1 to its own index.
            var expected = -1;
            winnerIdx.compareAndSwap(expected, i);
        }
    }

    totalTimer.stop();

    const winner = winnerIdx.read();
    if winner >= 0 {
        if verbose then
            writeln("\nSpeculative winner: ", results[winner].prover,
                    " in ", totalTimer.elapsed(), " s wall");
        return results[winner];
    }

    return new ProofResult(
        success = false, prover = "", proverId = -1,
        time = totalTimer.elapsed(), exitCode = -1,
        output = "All provers exhausted (speculative)",
        category = ProverCategory.InteractiveAssistant
    );
}

// Category-filtered parallel search — only try provers from a specific category
proc categorySearch(goal: string, provers: [] ProverInfo,
                     category: ProverCategory,
                     timeout: int = defaultTimeout): ProofResult {
    var filtered: list(ProverInfo);
    for p in provers {
        if p.category == category then
            filtered.pushBack(p);
    }

    if verbose then
        writeln("Category search (", category, "): ",
               filtered.size, " provers");

    return parallelProofSearch(goal, filtered.toArray(), timeout);
}

// ---------------------------------------------------------------------------
// Main demonstration
// ---------------------------------------------------------------------------

proc main() {
    var provers = buildProverRegistry();

    writeln("╔═══════════════════════════════════════════════════════════╗");
    writeln("║  ECHIDNA Chapel Metalayer — 30-Prover Parallel Search    ║");
    writeln("╚═══════════════════════════════════════════════════════════╝");
    writeln();

    // Availability check
    writeln("Prover availability:");
    var availCount = 0;
    for p in provers {
        var avail = isProverAvailable(p);
        if avail then availCount += 1;
        if verbose then
            writeln("  ", if avail then "✓" else "✗", " ", p.name,
                   " (", p.executable, ") — ", p.category);
    }
    writeln();
    writeln("Available: ", availCount, "/", provers.size);
    writeln();

    // Example: SMT-LIB goal (works with Z3, CVC5, Alt-Ergo)
    var smtGoal = "(set-logic QF_LIA)\n(declare-fun x () Int)\n(assert (= (+ x 1) (+ 1 x)))\n(check-sat)\n";

    writeln("═══════════════════════════════════════════════════════════");
    writeln("SMT Parallel Search");
    writeln("═══════════════════════════════════════════════════════════");
    var smtResult = categorySearch(smtGoal, provers, ProverCategory.SmtSolver, timeout=30);
    if smtResult.success then
        writeln("Best proof: ", smtResult.prover, " in ", smtResult.time, "s");
    writeln();

    // Full parallel search with a Lean goal
    var leanGoal = "theorem comm_add (n m : Nat) : n + m = m + n := Nat.add_comm n m\n";

    writeln("═══════════════════════════════════════════════════════════");
    writeln("Full 30-Prover Parallel Search (Lean goal)");
    writeln("═══════════════════════════════════════════════════════════");
    var fullResult = parallelProofSearch(leanGoal, provers, timeout=60);
    if fullResult.success then
        writeln("Best proof: ", fullResult.prover, " in ", fullResult.time, "s");

    writeln();
    writeln("╔═══════════════════════════════════════════════════════════╗");
    writeln("║  Chapel Metalayer Complete                                ║");
    writeln("╚═══════════════════════════════════════════════════════════╝");
}
