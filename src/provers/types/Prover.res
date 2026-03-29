// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)

/**
 * ECHIDNA Prover Types
 * Core type definitions for the neurosymbolic theorem proving platform
 */

/** Supported input formats for theorem provers */
type inputFormat =
  | @as("tptp") TPTP
  | @as("smtlib2") SMTLIB2
  | @as("metamath") Metamath
  | @as("lean") Lean
  | @as("wolfram") Wolfram
  | @as("dimacs") DIMACS
  | @as("natural") Natural

/** Result status from a prover */
type proverStatus =
  | @as("theorem") Theorem
  | @as("countersatisfiable") Countersatisfiable
  | @as("satisfiable") Satisfiable
  | @as("unsatisfiable") Unsatisfiable
  | @as("timeout") Timeout
  | @as("unknown") Unknown
  | @as("error") Error
  | @as("running") Running

/** Prover tier level (1=core, 4=experimental) */
type proverTier = Tier1 | Tier2 | Tier3 | Tier4

/** A single prover system */
type prover = {
  id: string,
  name: string,
  version: option<string>,
  formats: array<inputFormat>,
  endpoint: option<string>,
  tier: int,
  online: bool,
}

/** Result from a prover attempt */
type proverResult = {
  prover: string,
  status: proverStatus,
  proof: option<string>,
  model: option<string>,
  time_ms: float,
  raw_output: option<string>,
  error: option<string>,
  timestamp: Js.Date.t,
}

/** A problem to be proved */
type problem = {
  id: string,
  name: option<string>,
  format: inputFormat,
  content: string,
  expected: option<proverStatus>,
  timeout_sec: option<int>,
  metadata: option<Js.Dict.t<Js.Json.t>>,
}

/** Queue item for continuous runner */
type queueItem = {
  problem: problem,
  provers: array<string>,
  priority: int,
  created: Js.Date.t,
  mutable attempts: int,
  mutable results: array<proverResult>,
}

/** Configuration for prover clients */
type proverConfig = {
  timeout_sec: int,
  retry_count: int,
  retry_delay_ms: int,
  api_key: option<string>,
  endpoint: option<string>,
}

/** Default configuration */
let defaultConfig: proverConfig = {
  timeout_sec: 60,
  retry_count: 3,
  retry_delay_ms: 1000,
  api_key: None,
  endpoint: None,
}

/** Available provers registry */
let proverRegistry: Js.Dict.t<prover> = {
  let dict = Js.Dict.empty()

  // Tier 1 - Core provers
  Js.Dict.set(dict, "z3", {
    id: "z3", name: "Z3", version: None, formats: [SMTLIB2], endpoint: None, tier: 1, online: true,
  })
  Js.Dict.set(dict, "cvc5", {
    id: "cvc5", name: "CVC5", version: None, formats: [SMTLIB2], endpoint: None, tier: 1, online: true,
  })
  Js.Dict.set(dict, "vampire", {
    id: "vampire", name: "Vampire", version: None, formats: [TPTP], endpoint: None, tier: 1, online: true,
  })
  Js.Dict.set(dict, "e", {
    id: "e", name: "E Theorem Prover", version: None, formats: [TPTP], endpoint: None, tier: 1, online: true,
  })

  // Tier 2 - Big Six completion
  Js.Dict.set(dict, "metamath", {
    id: "metamath", name: "Metamath", version: None, formats: [Metamath], endpoint: None, tier: 2, online: true,
  })
  Js.Dict.set(dict, "isabelle", {
    id: "isabelle", name: "Isabelle/HOL", version: None, formats: [TPTP], endpoint: None, tier: 2, online: true,
  })
  Js.Dict.set(dict, "hol-light", {
    id: "hol-light", name: "HOL Light", version: None, formats: [TPTP], endpoint: None, tier: 2, online: true,
  })
  Js.Dict.set(dict, "mizar", {
    id: "mizar", name: "Mizar", version: None, formats: [TPTP], endpoint: None, tier: 2, online: true,
  })

  // Tier 3 - Extended support
  Js.Dict.set(dict, "lean", {
    id: "lean", name: "Lean 4", version: None, formats: [Lean], endpoint: None, tier: 3, online: true,
  })
  Js.Dict.set(dict, "coq", {
    id: "coq", name: "Coq/Rocq", version: None, formats: [TPTP], endpoint: None, tier: 3, online: true,
  })

  // SAT solvers
  Js.Dict.set(dict, "minisat", {
    id: "minisat", name: "MiniSat", version: None, formats: [DIMACS], endpoint: None, tier: 1, online: true,
  })
  Js.Dict.set(dict, "glucose", {
    id: "glucose", name: "Glucose", version: None, formats: [DIMACS], endpoint: None, tier: 1, online: true,
  })

  dict
}
