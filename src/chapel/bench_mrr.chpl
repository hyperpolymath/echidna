// SPDX-License-Identifier: AGPL-3.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Chapel speedup baseline — runs sequentialProofSearch,
// parallelProofSearch (best-of), and parallelProofSearchSpeculative
// against a small fixture corpus and emits three CSV tables:
//
//   1. wall-clock + winner       -> stdout
//   2. per-prover outcome rows   -> --telemetry-out
//   3. per-strategy summary      -> --summary-out
//
// Build: chpl -o bench_mrr bench_mrr.chpl
// Run:   ./bench_mrr --verbose=false --timeout=10
//
// Pass `--verbose=false` to keep progress chatter out of the stdout CSV;
// the `bench-chapel-mrr` Justfile recipe already does this.
//
// ---------------------------------------------------------------------------
// Output contracts (column names are stable; see docs/bench/)
// ---------------------------------------------------------------------------
//
// Stdout, one row per fixture x strategy:
//   fixture,strategy,wallclock_s,success,winning_prover
//
// Telemetry (--telemetry-out), one row per prover per fixture x strategy,
// so 4 fixtures x 3 strategies x 30 provers = 360 rows for the stock
// registry. Rows are never omitted: a prover the sequential strategy
// never reached is reported as `not_attempted` rather than dropped, so
// the per-strategy counts always sum to the registry size.
//   fixture,strategy,prover,prover_id,category,outcome,exit_code,wallclock_s
//
// `outcome` is one of:
//   completed_success  prover ran, exit status 0
//   completed_failure  prover ran and rejected the goal
//   preempted          exit -5, L2.3 SIGKILL by the speculative winner
//   timed_out          exit -3, wall timeout reached
//   not_available      exit -1, executable not on PATH (never invoked)
//   subprocess_error   exit -2 (temp-file write) or -4 (spawn/IO)
//   not_attempted      sequential returned before reaching this prover
//
// Summary (--summary-out), one row per fixture x strategy plus one
// `ALL` row per strategy aggregating the corpus. Preemption rate is
// `preempted / attempted_total`, so it is measured against provers that
// actually ran, not against the whole registry.
//   fixture,strategy,attempted_total,completed_success,completed_failure,
//   preempted,timed_out,not_available,subprocess_error,not_attempted,
//   preemption_rate,wallclock_s,success,winning_prover
//
// --telemetry-only=true omits the stdout wall-clock CSV, so a run
// produces only the two files. The searches themselves still execute —
// an outcome cannot be observed without invoking the prover — and the
// timing values inside the two files stay populated, because they are
// already measured and cost nothing to keep. The flag is about not
// emitting the timing table, not about avoiding the work.
//
// The fixture corpus is intentionally tiny (one trivially-true goal
// per available prover language) so the bench completes in well
// under one minute even on a cold cache. Real corpus-scale numbers
// are tracked in docs/handover/TODO.adoc.

use parallel_proof_search;
use Time;
use IO;

config const timeout = 10;
config const fixtureDir = "../../tests/chapel_fixtures";
config const telemetryOut = "bench_mrr_telemetry.csv";
config const summaryOut = "bench_mrr_summary.csv";
config const telemetryOnly = false;

record Fixture {
    var name: string;
    var path: string;
}

// Tally of `ProverOutcome` values for one fixture x strategy cell.
// `attempted_total` excludes `not_attempted` by construction, because a
// preemption rate over provers that were never invoked would be
// meaningless.
record OutcomeCounts {
    var attempted_total: int = 0;
    var completed_success: int = 0;
    var completed_failure: int = 0;
    var preempted: int = 0;
    var timed_out: int = 0;
    var not_available: int = 0;
    var subprocess_error: int = 0;
    var not_attempted: int = 0;
}

proc loadFixture(name: string, path: string): string throws {
    var f = open(path, ioMode.r);
    var r = f.reader();
    var buf: string;
    r.readAll(buf);
    r.close();
    f.close();
    return buf;
}

// ---------------------------------------------------------------------------
// Tallying
// ---------------------------------------------------------------------------

proc tallyOutcome(ref c: OutcomeCounts, o: ProverOutcome) {
    if o == ProverOutcome.NotAttempted {
        c.not_attempted += 1;
        return;
    }

    c.attempted_total += 1;

    // Plain if/else-if rather than `select`: the branches are
    // statements, not returns, and this keeps exhaustiveness obvious.
    if o == ProverOutcome.CompletedSuccess then c.completed_success += 1;
    else if o == ProverOutcome.CompletedFailure then c.completed_failure += 1;
    else if o == ProverOutcome.Preempted then c.preempted += 1;
    else if o == ProverOutcome.TimedOut then c.timed_out += 1;
    else if o == ProverOutcome.NotAvailable then c.not_available += 1;
    else if o == ProverOutcome.SubprocessError then c.subprocess_error += 1;
}

proc addCounts(ref dst: OutcomeCounts, const ref src: OutcomeCounts) {
    dst.attempted_total   += src.attempted_total;
    dst.completed_success += src.completed_success;
    dst.completed_failure += src.completed_failure;
    dst.preempted         += src.preempted;
    dst.timed_out         += src.timed_out;
    dst.not_available     += src.not_available;
    dst.subprocess_error  += src.subprocess_error;
    dst.not_attempted     += src.not_attempted;
}

// Preempted as a fraction of provers that actually ran. Rendered with
// the same width as the wallclock column so the two line up in a table.
proc preemptionRate(const ref c: OutcomeCounts): real {
    if c.attempted_total == 0 then return 0.0;
    return c.preempted:real / c.attempted_total:real;
}

// ---------------------------------------------------------------------------
// CSV line builders
// ---------------------------------------------------------------------------

proc wallclockLine(fixture: string, strategy: string, wall: real,
                   res: ProofResult): string {
    return fixture + "," + strategy + "," + wall:string + ","
         + (if res.success then "true" else "false") + ","
         + (if res.success then res.prover else "—");
}

proc telemetryLine(fixture: string, strategy: string, p: ProverInfo,
                   r: ProofResult, o: ProverOutcome, wall: real): string {
    return fixture + "," + strategy + "," + p.name + "," + p.id:string + ","
         + categoryLabel(p.category) + "," + outcomeLabel(o) + ","
         + r.exitCode:string + "," + wall:string;
}

proc summaryLine(fixture: string, strategy: string, const ref c: OutcomeCounts,
                 wall: real, res: ProofResult): string {
    return fixture + "," + strategy + ","
         + c.attempted_total:string + "," + c.completed_success:string + ","
         + c.completed_failure:string + "," + c.preempted:string + ","
         + c.timed_out:string + "," + c.not_available:string + ","
         + c.subprocess_error:string + "," + c.not_attempted:string + ","
         + preemptionRate(c):string + "," + wall:string + ","
         + (if res.success then "true" else "false") + ","
         + (if res.success then res.prover else "—");
}

// Corpus-level row: wall-clock sums across fixtures; there is no single
// winning prover, so those two columns are left empty.
proc corpusSummaryLine(strategy: string, const ref c: OutcomeCounts,
                       wall: real): string {
    return "ALL," + strategy + ","
         + c.attempted_total:string + "," + c.completed_success:string + ","
         + c.completed_failure:string + "," + c.preempted:string + ","
         + c.timed_out:string + "," + c.not_available:string + ","
         + c.subprocess_error:string + "," + c.not_attempted:string + ","
         + preemptionRate(c):string + "," + wall:string + ",,";
}

// ---------------------------------------------------------------------------
// Strategy dispatch
// ---------------------------------------------------------------------------

// Index into the strategy list below. Returns the same verdict the
// public (telemetry-free) strategy procs return, while filling the
// per-prover table.
proc runStrategy(si: int, goal: string, provers: [] ProverInfo,
                 ref results: [] ProofResult, ref attempted: [] bool,
                 timeout: int): ProofResult {
    if si == 0 {
        return sequentialProofSearchTelemetry(goal, provers, results, attempted, timeout);
    } else if si == 1 {
        return parallelProofSearchTelemetry(goal, provers, results, attempted, timeout);
    } else {
        return parallelProofSearchSpeculativeTelemetry(goal, provers, results, attempted, timeout);
    }
}

proc main(): int {
    var allProvers = buildProverRegistry();

    const fixtures: [0..3] Fixture = [
        new Fixture("coq_trivial",    fixtureDir + "/coq_trivial.v"),
        new Fixture("lean_trivial",   fixtureDir + "/lean_trivial.lean"),
        new Fixture("idris2_trivial", fixtureDir + "/idris2_trivial.idr"),
        new Fixture("agda_trivial",   fixtureDir + "/agda_trivial.agda")
    ];

    const strategyNames: [0..2] string = [
        "sequential", "parallel_bestof", "parallel_speculative"
    ];

    const wallclockHeader =
        "fixture,strategy,wallclock_s,success,winning_prover";
    const telemetryHeader =
        "fixture,strategy,prover,prover_id,category,outcome,exit_code,wallclock_s";
    const summaryHeader =
        "fixture,strategy,attempted_total,completed_success,completed_failure,"
        + "preempted,timed_out,not_available,subprocess_error,not_attempted,"
        + "preemption_rate,wallclock_s,success,winning_prover";

    var teleFile = open(telemetryOut, ioMode.cw);
    var teleW = teleFile.writer(locking=false);
    var sumFile = open(summaryOut, ioMode.cw);
    var sumW = sumFile.writer(locking=false);

    teleW.write(telemetryHeader + "\n");
    sumW.write(summaryHeader + "\n");

    if !telemetryOnly then
        writeln(wallclockHeader);

    var corpusTotals: [strategyNames.domain] OutcomeCounts;
    var corpusWall: [strategyNames.domain] real;

    for fx in fixtures {
        var goal: string;
        try {
            goal = loadFixture(fx.name, fx.path);
        } catch e {
            if !telemetryOnly then
                writeln(fx.name, ",LOAD_ERROR,0.0,false,", e.message());
            continue;
        }

        for si in strategyNames.domain {
            const strategy = strategyNames[si];

            var results: [allProvers.domain] ProofResult;
            var attempted: [allProvers.domain] bool;

            var t = new stopwatch();
            t.start();
            const verdict = runStrategy(si, goal, allProvers, results, attempted, timeout);
            t.stop();
            const wall = t.elapsed();

            if !telemetryOnly then
                writeln(wallclockLine(fx.name, strategy, wall, verdict));

            // One telemetry row per registry entry, always.
            var counts: OutcomeCounts;
            for i in allProvers.domain {
                const o = classifyOutcome(results[i], attempted[i]);
                tallyOutcome(counts, o);
                teleW.write(telemetryLine(fx.name, strategy, allProvers[i],
                                          results[i], o, wall) + "\n");
            }

            sumW.write(summaryLine(fx.name, strategy, counts, wall, verdict) + "\n");
            addCounts(corpusTotals[si], counts);
            corpusWall[si] += wall;
        }
    }

    for si in strategyNames.domain {
        sumW.write(corpusSummaryLine(strategyNames[si], corpusTotals[si],
                                     corpusWall[si]) + "\n");
    }

    teleW.close();
    teleFile.close();
    sumW.close();
    sumFile.close();

    if verbose {
        writeln("\nWrote per-prover telemetry -> ", telemetryOut);
        writeln("Wrote per-strategy summary -> ", summaryOut);
    }

    return 0;
}
