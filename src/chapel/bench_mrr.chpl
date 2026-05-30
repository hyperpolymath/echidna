// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Chapel speedup baseline — runs sequentialProofSearch,
// parallelProofSearch (best-of), and parallelProofSearchSpeculative
// against a small fixture corpus and emits a CSV table comparing
// wall-clock time and the winning prover.
//
// Build: chpl -o bench_mrr bench_mrr.chpl
// Run:   ./bench_mrr  --timeout=10
//
// CSV columns: fixture,strategy,wallclock_s,success,winning_prover
//
// The fixture corpus is intentionally tiny (one trivially-true goal
// per available prover language) so the bench completes in well
// under one minute even on a cold cache. Real corpus-scale numbers
// are tracked in docs/handover/TODO.md.

use parallel_proof_search;
use Time;
use IO;

config const timeout = 10;
config const fixtureDir = "../../tests/chapel_fixtures";

record Fixture {
    var name: string;
    var path: string;
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

proc benchOne(goal: string, fixtureName: string, allProvers: [] ProverInfo,
              timeout: int) {

    // sequential
    {
        var t = new stopwatch();
        t.start();
        const res = sequentialProofSearch(goal, allProvers, timeout);
        t.stop();
        writef("%s,sequential,%.3dr,%s,%s\n",
               fixtureName, t.elapsed(),
               if res.success then "true" else "false",
               if res.success then res.prover else "—");
    }

    // parallel best-of (waits for all)
    {
        var t = new stopwatch();
        t.start();
        const res = parallelProofSearch(goal, allProvers, timeout);
        t.stop();
        writef("%s,parallel_bestof,%.3dr,%s,%s\n",
               fixtureName, t.elapsed(),
               if res.success then "true" else "false",
               if res.success then res.prover else "—");
    }

    // parallel speculative (first-success-wins)
    {
        var t = new stopwatch();
        t.start();
        const res = parallelProofSearchSpeculative(goal, allProvers, timeout);
        t.stop();
        writef("%s,parallel_speculative,%.3dr,%s,%s\n",
               fixtureName, t.elapsed(),
               if res.success then "true" else "false",
               if res.success then res.prover else "—");
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

    writeln("fixture,strategy,wallclock_s,success,winning_prover");
    for fx in fixtures {
        var goal: string;
        try {
            goal = loadFixture(fx.name, fx.path);
        } catch e {
            writef("%s,LOAD_ERROR,0.0,false,%s\n", fx.name, e.message());
            continue;
        }
        benchOne(goal, fx.name, allProvers, timeout);
    }
    return 0;
}
