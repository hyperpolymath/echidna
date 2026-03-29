// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)

/**
 * ECHIDNA Prover Types Tests
 * Validates core type definitions and default configuration values.
 *
 * Note: These are structural tests expressed as ReScript assertions.
 * In a full test harness, use a ReScript-compatible test runner.
 */

/** Verify DEFAULT_CONFIG has required fields with expected values */
let testDefaultConfig = () => {
  let config = Prover.defaultConfig
  assert(config.timeout_sec == 60)
  assert(config.retry_count == 3)
  assert(config.retry_delay_ms == 1000)
  Js.log("[ProverTest] DEFAULT_CONFIG - has required fields: PASS")
}

/** Verify PROVER_REGISTRY contains expected provers */
let testProverRegistry = () => {
  let registry = Prover.proverRegistry
  let z3 = Js.Dict.get(registry, "z3")
  let vampire = Js.Dict.get(registry, "vampire")
  let metamath = Js.Dict.get(registry, "metamath")

  switch (z3, vampire, metamath) {
  | (Some(z3p), Some(_vamp), Some(mmp)) => {
      assert(z3p.tier == 1)
      assert(mmp.tier == 2)
      Js.log("[ProverTest] PROVER_REGISTRY - contains expected provers: PASS")
    }
  | _ => {
      Js.log("[ProverTest] PROVER_REGISTRY - missing expected provers: FAIL")
      assert(false)
    }
  }
}

/** Verify Problem type can be created with valid fields */
let testProblemType = () => {
  let problem: Prover.problem = {
    id: "test-problem-1",
    name: Some("Test Problem"),
    format: Prover.TPTP,
    content: "fof(test, axiom, p).",
    expected: Some(Prover.Theorem),
    timeout_sec: Some(30),
    metadata: Some(Js.Dict.fromArray([("source", Js.Json.string("test"))])),
  }

  assert(problem.id == "test-problem-1")
  assert(problem.format == Prover.TPTP)
  assert(Js.String2.length(problem.content) > 0)
  Js.log("[ProverTest] Problem type - can create valid problem: PASS")
}

/** Verify ProverResult type can be created with valid fields */
let testProverResultType = () => {
  let result: Prover.proverResult = {
    prover: "z3-wasm",
    status: Prover.Theorem,
    proof: Some("QED"),
    model: None,
    time_ms: 123.0,
    raw_output: None,
    error: None,
    timestamp: Js.Date.make(),
  }

  assert(result.prover == "z3-wasm")
  assert(result.status == Prover.Theorem)
  Js.log("[ProverTest] ProverResult type - can create valid result: PASS")
}

/** Run all tests */
let runAll = () => {
  Js.log("=== ECHIDNA Prover Types Tests ===")
  testDefaultConfig()
  testProverRegistry()
  testProblemType()
  testProverResultType()
  Js.log("=== All prover type tests passed ===")
}

let _ = runAll()
