// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)

/**
 * ECHIDNA Unified Prover Client
 * Aggregates all prover backends into a single interface.
 */

/** Prover selection strategy */
type selectionStrategy =
  | First
  | Fastest
  | All
  | Cascade
  | Parallel

/** Result from unified solving */
type unifiedResult = {
  problem: Prover.problem,
  results: array<Prover.proverResult>,
  bestResult: option<Prover.proverResult>,
  strategy: selectionStrategy,
  totalTime_ms: float,
}

/** Service health status */
type serviceHealth = {
  name: string,
  available: bool,
  latency_ms: option<float>,
  provers: int,
  lastCheck: Js.Date.t,
}

/** Client backend entry */
type clientBackend = {
  name: string,
  provers: array<Prover.prover>,
  ping: unit => Js.Promise2.t<bool>,
  solve: (Prover.proverConfig, Prover.problem, ~proverId: string) => Js.Promise2.t<Prover.proverResult>,
}

/** Client name identifier */
let name = "ECHIDNA-Unified"

/** Initialize all client backends and collect their provers */
let makeBackends = (config: Prover.proverConfig): array<clientBackend> => {
  [
    {
      name: SystemOnTptp.name,
      provers: SystemOnTptp.tptpProvers,
      ping: SystemOnTptp.ping,
      solve: (cfg, prob, ~proverId) => SystemOnTptp.solve(cfg, prob, ~proverId),
    },
    {
      name: Metamath.name,
      provers: Metamath.provers,
      ping: Metamath.ping,
      solve: (cfg, prob, ~proverId as _) => Metamath.solve(prob),
    },
    {
      name: Z3Wasm.fallbackName,
      provers: Z3Wasm.fallbackProvers,
      ping: Z3Wasm.fallbackPing,
      solve: (cfg, prob, ~proverId) => Z3Wasm.fallbackSolve(cfg, prob, ~proverId=Some(proverId)),
    },
    {
      name: Wolfram.name,
      provers: Wolfram.provers,
      ping: () => Wolfram.ping(config),
      solve: (cfg, prob, ~proverId) => Wolfram.solve(cfg, prob, ~proverId),
    },
    {
      name: LeanTool.name,
      provers: LeanTool.provers,
      ping: () => LeanTool.ping(config),
      solve: (cfg, prob, ~proverId) => LeanTool.solve(cfg, prob, ~proverId),
    },
  ]
}

/** Build a prover-to-backend mapping */
let buildProverMap = (backends: array<clientBackend>): Js.Dict.t<clientBackend> => {
  let map = Js.Dict.empty()
  backends->Belt.Array.forEach(backend => {
    backend.provers->Belt.Array.forEach(p => {
      Js.Dict.set(map, p.id, backend)
    })
  })
  map
}

/** Collect all provers from all backends */
let allProvers = (backends: array<clientBackend>): array<Prover.prover> => {
  backends->Belt.Array.flatMap(b => b.provers)
}

/** Check if status indicates success */
let isSuccessful = (status: Prover.proverStatus): bool => {
  switch status {
  | Prover.Theorem | Prover.Unsatisfiable | Prover.Satisfiable => true
  | _ => false
  }
}

/** Ping at least one backend */
let ping = (backends: array<clientBackend>): Js.Promise2.t<bool> => {
  backends
  ->Belt.Array.map(b => b.ping())
  ->Js.Promise2.all
  ->Js.Promise2.then(results => {
    Js.Promise2.resolve(results->Belt.Array.some(ok => ok))
  })
}

/** List all provers from all backends */
let listProvers = (backends: array<clientBackend>): Js.Promise2.t<array<Prover.prover>> => {
  Js.Promise2.resolve(allProvers(backends))
}

/** Check health of all services */
let healthCheck = (backends: array<clientBackend>): Js.Promise2.t<array<serviceHealth>> => {
  backends
  ->Belt.Array.map(backend => {
    let start = Js.Date.now()
    backend.ping()
    ->Js.Promise2.then(available => {
      Js.Promise2.resolve({
        name: backend.name,
        available,
        latency_ms: Some(Js.Date.now() -. start),
        provers: Belt.Array.length(backend.provers),
        lastCheck: Js.Date.make(),
      })
    })
    ->Js.Promise2.catch(_ => {
      Js.Promise2.resolve({
        name: backend.name,
        available: false,
        latency_ms: None,
        provers: Belt.Array.length(backend.provers),
        lastCheck: Js.Date.make(),
      })
    })
  })
  ->Js.Promise2.all
}

/** Solve a single problem, optionally specifying a prover */
let solve = (
  config: Prover.proverConfig,
  backends: array<clientBackend>,
  problem: Prover.problem,
  ~proverId: option<string>=?,
): Js.Promise2.t<Prover.proverResult> => {
  let proverMap = buildProverMap(backends)

  switch proverId {
  | Some(pid) =>
    switch Js.Dict.get(proverMap, pid) {
    | Some(backend) => backend.solve(config, problem, ~proverId=pid)
    | None =>
      Js.Promise2.resolve({
        Prover.prover: pid,
        status: Prover.Error,
        proof: None,
        model: None,
        time_ms: 0.0,
        raw_output: None,
        error: Some(`Unknown prover: ${pid}`),
        timestamp: Js.Date.make(),
      })
    }
  | None => {
      // Select based on format
      let formatClients = switch problem.format {
      | Prover.TPTP => ["SystemOnTPTP"]
      | Prover.SMTLIB2 => ["Z3-Fallback", "SystemOnTPTP"]
      | Prover.Metamath => ["Metamath"]
      | Prover.Lean => ["LeanTool"]
      | Prover.Wolfram | Prover.Natural => ["WolframAlpha"]
      | Prover.DIMACS => ["SystemOnTPTP"]
      }

      let selectedBackend = formatClients->Belt.Array.reduce(None, (acc, clientName) => {
        switch acc {
        | Some(_) => acc
        | None => backends->Belt.Array.getBy(b => b.name == clientName)
        }
      })

      switch selectedBackend {
      | Some(backend) =>
        let defaultProver = switch Belt.Array.get(backend.provers, 0) {
        | Some(p) => p.id
        | None => "unknown"
        }
        backend.solve(config, problem, ~proverId=defaultProver)
      | None =>
        switch Belt.Array.get(backends, 0) {
        | Some(backend) =>
          let pid = switch Belt.Array.get(backend.provers, 0) {
          | Some(p) => p.id
          | None => "unknown"
          }
          backend.solve(config, problem, ~proverId=pid)
        | None =>
          Js.Promise2.resolve({
            Prover.prover: "unknown",
            status: Prover.Error,
            proof: None,
            model: None,
            time_ms: 0.0,
            raw_output: None,
            error: Some(`No client available for format`),
            timestamp: Js.Date.make(),
          })
        }
      }
    }
  }
}

/** Select appropriate provers for a problem based on its format */
let selectProversForProblem = (problem: Prover.problem): array<string> => {
  switch problem.format {
  | Prover.TPTP => ["Vampire---4.8", "E---3.0", "Z3---4.12.2", "CVC5---1.0.8"]
  | Prover.SMTLIB2 => ["z3-wasm", "Z3---4.12.2", "CVC5---1.0.8"]
  | Prover.Metamath => ["metamath-verify"]
  | Prover.Lean => ["lean4", "lean4-mathlib"]
  | Prover.Wolfram => ["wolfram-prove", "wolfram-solve"]
  | Prover.Natural => ["wolfram-prove"]
  | Prover.DIMACS => ["MiniSat---2.2.1", "Glucose---4.2.1"]
  }
}

/** Solve with a specified strategy */
let solveWithStrategy = (
  config: Prover.proverConfig,
  backends: array<clientBackend>,
  problem: Prover.problem,
  ~strategy: selectionStrategy=Cascade,
  ~provers: option<array<string>>=?,
): Js.Promise2.t<unifiedResult> => {
  let startTime = Js.Date.now()
  let targetProvers = switch provers {
  | Some(ps) => ps
  | None => selectProversForProblem(problem)
  }

  switch strategy {
  | First => {
      let pid = switch Belt.Array.get(targetProvers, 0) {
      | Some(p) => p
      | None => "unknown"
      }
      solve(config, backends, problem, ~proverId=Some(pid))
      ->Js.Promise2.then(result => {
        Js.Promise2.resolve({
          problem,
          results: [result],
          bestResult: Some(result),
          strategy: First,
          totalTime_ms: Js.Date.now() -. startTime,
        })
      })
    }

  | Cascade => {
      let rec tryNext = (remaining: array<string>, acc: array<Prover.proverResult>): Js.Promise2.t<unifiedResult> => {
        switch Belt.Array.get(remaining, 0) {
        | None =>
          Js.Promise2.resolve({
            problem,
            results: acc,
            bestResult: None,
            strategy: Cascade,
            totalTime_ms: Js.Date.now() -. startTime,
          })
        | Some(pid) =>
          solve(config, backends, problem, ~proverId=Some(pid))
          ->Js.Promise2.then(result => {
            let newAcc = Belt.Array.concat(acc, [result])
            if isSuccessful(result.status) {
              Js.Promise2.resolve({
                problem,
                results: newAcc,
                bestResult: Some(result),
                strategy: Cascade,
                totalTime_ms: Js.Date.now() -. startTime,
              })
            } else {
              tryNext(Belt.Array.sliceToEnd(remaining, 1), newAcc)
            }
          })
        }
      }
      tryNext(targetProvers, [])
    }

  | Parallel | All | Fastest => {
      targetProvers
      ->Belt.Array.map(pid => solve(config, backends, problem, ~proverId=Some(pid)))
      ->Js.Promise2.all
      ->Js.Promise2.then(results => {
        let successful = results->Belt.Array.keep(r => isSuccessful(r.status))
        let bestResult = if Belt.Array.length(successful) > 0 {
          successful->Belt.Array.reduce(None, (acc, r) => {
            switch acc {
            | None => Some(r)
            | Some(best) => if r.time_ms < best.time_ms { Some(r) } else { acc }
            }
          })
        } else {
          Belt.Array.get(results, 0)
        }

        Js.Promise2.resolve({
          problem,
          results,
          bestResult,
          strategy,
          totalTime_ms: Js.Date.now() -. startTime,
        })
      })
    }
  }
}

/** Get statistics about available provers and backends */
let getStats = (backends: array<clientBackend>): {
  "totalProvers": int,
  "backends": int,
} => {
  {
    "totalProvers": allProvers(backends)->Belt.Array.length,
    "backends": Belt.Array.length(backends),
  }
}
