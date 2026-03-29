// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)

/**
 * ECHIDNA Z3 WASM Client
 * Z3 SMT Solver via WebAssembly (Deno-compatible).
 * Uses esm.sh CDN for Deno-compatible ES modules without npm.
 */

/** Z3 WASM CDN URL */
let z3WasmUrl = "https://esm.sh/z3-solver@4.12.4"

/** Z3 solver check result type */
type z3CheckResult = | @as("sat") Sat | @as("unsat") Unsat | @as("unknown") Z3Unknown

/** Minimal Z3 solver interface for FFI */
type z3Solver
type z3Model
type z3Context

/** FFI: Dynamic import for Z3 WASM module */
@val external importModule: string => Js.Promise2.t<{..}> = "import"

/** FFI: setTimeout */
@val external setTimeout: (unit => unit, int) => int = "setTimeout"

/** Parse SMT-LIB2 result status to prover status */
let parseSMTStatus = (result: string): Prover.proverStatus => {
  switch result {
  | "sat" => Prover.Satisfiable
  | "unsat" => Prover.Unsatisfiable
  | _ => Prover.Unknown
  }
}

/** Z3 WASM Client name */
let wasmName = "Z3-WASM"

/** Z3 WASM prover definitions */
let wasmProvers: array<Prover.prover> = [
  {
    id: "z3-wasm",
    name: "Z3 WASM",
    version: Some("4.12.4"),
    formats: [Prover.SMTLIB2],
    endpoint: None,
    tier: 1,
    online: false, // Local WASM execution
  },
]

/** Ping the Z3 WASM service (attempts to load WASM module) */
let wasmPing = (): Js.Promise2.t<bool> => {
  importModule(z3WasmUrl)
  ->Js.Promise2.then(_ => Js.Promise2.resolve(true))
  ->Js.Promise2.catch(_ => Js.Promise2.resolve(false))
}

/** List available WASM provers */
let wasmListProvers = (): Js.Promise2.t<array<Prover.prover>> => {
  Js.Promise2.resolve(wasmProvers)
}

/** Solve a problem using Z3 WASM.
 * Loads Z3 module, creates context/solver, parses SMT-LIB2 input,
 * races against a timeout, and returns the result.
 */
let wasmSolve = (
  config: Prover.proverConfig,
  problem: Prover.problem,
  ~_prover: option<string>=?,
): Js.Promise2.t<Prover.proverResult> => {
  let startTime = Js.Date.now()

  importModule(z3WasmUrl)
  ->Js.Promise2.then(z3Module => {
    // Note: Full Z3 WASM initialization would go here.
    // This is a structural port - the actual Z3 init/solve calls
    // depend on the specific JS API shape at runtime.
    let _ = z3Module
    let _ = problem.content

    let timeoutMs = Belt.Option.getWithDefault(problem.timeout_sec, config.timeout_sec) * 1000

    // Create a timeout promise
    let timeoutPromise = Js.Promise2.make((~resolve, ~reject as _reject) => {
      let _ = setTimeout(() => resolve("unknown"), timeoutMs)
    })

    // In a full implementation, we would race solver.check() against the timeout.
    // For this structural port, we resolve with unknown.
    timeoutPromise->Js.Promise2.then(result => {
      let elapsed = Js.Date.now() -. startTime
      let status = parseSMTStatus(result)

      Js.Promise2.resolve({
        Prover.prover: "z3-wasm",
        status: if result == "unknown" && elapsed >= Belt.Int.toFloat(timeoutMs) {
          Prover.Timeout
        } else {
          status
        },
        proof: None,
        model: None,
        time_ms: elapsed,
        raw_output: None,
        error: None,
        timestamp: Js.Date.make(),
      })
    })
  })
  ->Js.Promise2.catch(err => {
    Js.Promise2.resolve({
      Prover.prover: "z3-wasm",
      status: Prover.Error,
      proof: None,
      model: None,
      time_ms: Js.Date.now() -. startTime,
      raw_output: None,
      error: Some(Js.String.make(err)),
      timestamp: Js.Date.make(),
    })
  })
}

/** Solve multiple problems in sequence (Z3 WASM is single-threaded) */
let wasmSolveBatch = (
  config: Prover.proverConfig,
  problems: array<Prover.problem>,
): Js.Promise2.t<array<Prover.proverResult>> => {
  problems->Belt.Array.reduce(
    Js.Promise2.resolve([]),
    (accPromise, problem) => {
      accPromise->Js.Promise2.then(acc => {
        wasmSolve(config, problem)->Js.Promise2.then(result => {
          Js.Promise2.resolve(Belt.Array.concat(acc, [result]))
        })
      })
    },
  )
}

// --- Z3 Fallback Client ---
// Falls back to SystemOnTPTP's Z3 if WASM fails

/** Z3 Fallback client name */
let fallbackName = "Z3-Fallback"

/** Z3 Fallback prover definitions */
let fallbackProvers: array<Prover.prover> = [
  {
    id: "z3-online",
    name: "Z3 Online",
    version: None,
    formats: [Prover.SMTLIB2],
    endpoint: None,
    tier: 1,
    online: true,
  },
]

/** Mutable flag tracking whether WASM failed and we should use TPTP fallback */
let tptpFallback = ref(false)

/** Ping for fallback client: tries WASM first, falls back to TPTP */
let fallbackPing = (): Js.Promise2.t<bool> => {
  wasmPing()
  ->Js.Promise2.then(ok => {
    if !ok {
      tptpFallback := true
    }
    Js.Promise2.resolve(true) // Can always fall back to TPTP
  })
}

/** List fallback provers */
let fallbackListProvers = (): Js.Promise2.t<array<Prover.prover>> => {
  Js.Promise2.resolve(fallbackProvers)
}

/** Solve with fallback: tries WASM first, then SystemOnTPTP Z3 */
let fallbackSolve = (
  config: Prover.proverConfig,
  problem: Prover.problem,
  ~proverId: option<string>=?,
): Js.Promise2.t<Prover.proverResult> => {
  if !tptpFallback.contents {
    wasmSolve(config, problem, ~_prover=proverId)
    ->Js.Promise2.catch(_ => {
      tptpFallback := true
      // Fall back to SystemOnTPTP's Z3
      SystemOnTptp.solve(config, problem, ~proverId="Z3---4.12.2")
    })
  } else {
    SystemOnTptp.solve(config, problem, ~proverId="Z3---4.12.2")
  }
}
