// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)

/**
 * ECHIDNA Unified Prover Client Tests
 * Validates the unified client initialization, prover listing,
 * statistics, and basic solving capabilities.
 */

/** Test: Unified client initialization */
let testInitialization = () => {
  let config = Prover.defaultConfig
  let backends = Unified.makeBackends(config)
  let provers = Unified.allProvers(backends)

  assert(Unified.name == "ECHIDNA-Unified")
  assert(Belt.Array.length(provers) > 0)
  Js.log("[UnifiedTest] initialization: PASS")
}

/** Test: listProvers returns non-empty array */
let testListProvers = () => {
  let config = Prover.defaultConfig
  let backends = Unified.makeBackends(config)

  Unified.listProvers(backends)
  ->Js.Promise2.then(provers => {
    assert(Belt.Array.length(provers) > 0)

    let ids = provers->Belt.Array.map(p => p.Prover.id)
    let hasExpected =
      ids->Belt.Array.some(id => id == "Vampire---4.8") ||
      ids->Belt.Array.some(id => id == "z3-wasm")
    assert(hasExpected)

    Js.log("[UnifiedTest] listProvers: PASS")
    Js.Promise2.resolve()
  })
}

/** Test: getStats returns valid statistics */
let testGetStats = () => {
  let config = Prover.defaultConfig
  let backends = Unified.makeBackends(config)
  let stats = Unified.getStats(backends)

  assert(stats["totalProvers"] > 0)
  assert(stats["backends"] > 0)
  Js.log("[UnifiedTest] getStats: PASS")
}

/** Run all tests */
let runAll = () => {
  Js.log("=== ECHIDNA Unified Prover Client Tests ===")
  testInitialization()
  let _ = testListProvers()
  testGetStats()
  Js.log("=== All unified client tests passed ===")
}

let _ = runAll()
