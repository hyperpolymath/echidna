// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Hello-Chapel smoke target.
//
// This file exists so the CI signal for "Chapel toolchain is healthy
// enough to compile + run a binary" is independent of the metalayer
// module's growing surface area. If `parallel_proof_search.chpl` is
// mid-refactor, `chapel-build` can still flag a toolchain regression
// here without ambiguity. Runtime: well under a second.

use Time;

config const greeting = "Hello, Chapel — ECHIDNA metalayer smoke OK";

proc main(): int {
  var t = new stopwatch();
  t.start();

  // Stress the three primitives the metalayer leans on so the smoke
  // result actually means something:
  //   - parallel task creation (`coforall`)
  //   - atomic compare-and-swap (used by speculative search)
  //   - reduction over a small array
  var winner: atomic int;
  winner.write(-1);

  coforall i in 1..8 {
    var expected = -1;
    if i == 3 then winner.compareAndSwap(expected, i);
  }

  const sum = + reduce (1..100);

  t.stop();

  writeln(greeting);
  writeln("  parallel-CAS winner: ", winner.read(), " (expected 3)");
  writeln("  reduction sum 1..100: ", sum, " (expected 5050)");
  writeln("  elapsed: ", t.elapsed(), " s");

  if winner.read() != 3 then return 2;
  if sum != 5050 then return 3;
  return 0;
}
