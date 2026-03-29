// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)

/**
 * ECHIDNA SystemOnTPTP Client
 * Connects to TPTP.org's SystemOnTPTP service (40+ theorem provers).
 */

/** SystemOnTPTP service URLs */
let systemOnTptpUrl = "https://www.tptp.org/cgi-bin/SystemOnTPTP"
let systemOnTptpForm = "https://www.tptp.org/cgi-bin/SystemOnTPTPFormReply"

/** Available provers on SystemOnTPTP */
let tptpProvers: array<Prover.prover> = [
  // First-order theorem provers
  {id: "Vampire---4.8", name: "Vampire 4.8", version: None, formats: [Prover.TPTP], endpoint: None, tier: 1, online: true},
  {id: "E---3.0", name: "E 3.0", version: None, formats: [Prover.TPTP], endpoint: None, tier: 1, online: true},
  {id: "iProver---3.8", name: "iProver 3.8", version: None, formats: [Prover.TPTP], endpoint: None, tier: 1, online: true},
  {id: "SPASS---3.9", name: "SPASS 3.9", version: None, formats: [Prover.TPTP], endpoint: None, tier: 2, online: true},
  {id: "Prover9---1109a", name: "Prover9", version: None, formats: [Prover.TPTP], endpoint: None, tier: 2, online: true},
  // SMT solvers
  {id: "Z3---4.12.2", name: "Z3 4.12.2", version: None, formats: [Prover.TPTP, Prover.SMTLIB2], endpoint: None, tier: 1, online: true},
  {id: "CVC5---1.0.8", name: "CVC5 1.0.8", version: None, formats: [Prover.TPTP, Prover.SMTLIB2], endpoint: None, tier: 1, online: true},
  // Higher-order provers
  {id: "Leo-III---1.7", name: "Leo-III 1.7", version: None, formats: [Prover.TPTP], endpoint: None, tier: 2, online: true},
  {id: "Satallax---3.5", name: "Satallax 3.5", version: None, formats: [Prover.TPTP], endpoint: None, tier: 2, online: true},
  {id: "Zipperposition---2.1", name: "Zipperposition 2.1", version: None, formats: [Prover.TPTP], endpoint: None, tier: 2, online: true},
  // Model finders
  {id: "Paradox---4.0", name: "Paradox 4.0", version: None, formats: [Prover.TPTP], endpoint: None, tier: 2, online: true},
  {id: "Mace4---0.5", name: "Mace4 0.5", version: None, formats: [Prover.TPTP], endpoint: None, tier: 2, online: true},
  // SAT solvers
  {id: "MiniSat---2.2.1", name: "MiniSat 2.2.1", version: None, formats: [Prover.DIMACS], endpoint: None, tier: 1, online: true},
  {id: "Glucose---4.2.1", name: "Glucose 4.2.1", version: None, formats: [Prover.DIMACS], endpoint: None, tier: 1, online: true},
  // Proof assistants (limited automation)
  {id: "Isabelle---2024", name: "Isabelle 2024", version: None, formats: [Prover.TPTP], endpoint: None, tier: 2, online: true},
]

/** Parse SZS status from TPTP output string */
let parseSZSStatus = (output: string): Prover.proverStatus => {
  let statusMatch = Js.String2.match_(output, %re("/SZS status (\\w+)/"))
  switch statusMatch {
  | Some(matches) if Belt.Array.length(matches) > 1 =>
    switch Js.Nullable.toOption(matches[1]) {
    | Some(status) => {
        let lower = Js.String2.toLowerCase(status)
        switch lower {
        | "theorem" => Prover.Theorem
        | "unsatisfiable" => Prover.Unsatisfiable
        | "satisfiable" => Prover.Satisfiable
        | "countersatisfiable" => Prover.Countersatisfiable
        | "timeout" | "resourceout" => Prover.Timeout
        | "gaveup" | "unknown" => Prover.Unknown
        | "error" => Prover.Error
        | _ => Prover.Unknown
        }
      }
    | None => Prover.Unknown
    }
  | _ => Prover.Unknown
  }
}

/** Parse timing from TPTP output */
let parseTime = (output: string): float => {
  let timeMatch = Js.String2.match_(output, %re("/(\\d+\\.?\\d*)\\s*s(?:econds?)?/i"))
  switch timeMatch {
  | Some(matches) if Belt.Array.length(matches) > 1 =>
    switch Js.Nullable.toOption(matches[1]) {
    | Some(timeStr) => Belt.Float.fromString(timeStr)->Belt.Option.getWithDefault(0.0) *. 1000.0
    | None => 0.0
    }
  | _ => 0.0
  }
}

/** Extract proof from SZS output block */
let extractProof = (output: string): option<string> => {
  let proofMatch = Js.String2.match_(output, %re("/SZS output start[\\s\\S]*?SZS output end/"))
  switch proofMatch {
  | Some(matches) if Belt.Array.length(matches) > 0 =>
    Js.Nullable.toOption(matches[0])
  | _ => None
  }
}

/** Client name identifier */
let name = "SystemOnTPTP"

/** Ping the SystemOnTPTP service */
let ping = (): Js.Promise2.t<bool> => {
  Http.getText(systemOnTptpUrl)
  ->Js.Promise2.then(response => {
    Js.Promise2.resolve(Js.String2.includes(response, "SystemOnTPTP"))
  })
  ->Js.Promise2.catch(_ => Js.Promise2.resolve(false))
}

/** List available provers */
let listProvers = (): Js.Promise2.t<array<Prover.prover>> => {
  Js.Promise2.resolve(tptpProvers)
}

/** Solve a problem using SystemOnTPTP */
let solve = (
  config: Prover.proverConfig,
  problem: Prover.problem,
  ~proverId: string="Vampire---4.8",
): Js.Promise2.t<Prover.proverResult> => {
  let startTime = Js.Date.now()
  let timeout = Belt.Option.getWithDefault(problem.timeout_sec, config.timeout_sec)

  let formData = Js.Dict.fromArray([
    ("TPTPProblem", ""),
    ("ProblemSource", "FORMULAE"),
    ("FORMULAEProblem", problem.content),
    ("QuietFlag", "-q2"),
    ("SubmitButton", "RunSelectedSystems"),
    (`System___${proverId}`, proverId),
    (`TimeLimit___${proverId}`, Belt.Int.toString(timeout)),
  ])

  Http.postForm(systemOnTptpForm, formData, ~options={
    maxRetries: config.retry_count,
    baseDelayMs: config.retry_delay_ms,
    maxDelayMs: 16000,
  })
  ->Js.Promise2.then(response => {
    let status = parseSZSStatus(response)
    let proof = extractProof(response)
    let elapsed = Js.Date.now() -. startTime
    let parsedTime = parseTime(response)

    Js.Promise2.resolve({
      Prover.prover: proverId,
      status,
      proof,
      model: None,
      time_ms: if parsedTime > 0.0 { parsedTime } else { elapsed },
      raw_output: Some(response),
      error: None,
      timestamp: Js.Date.make(),
    })
  })
  ->Js.Promise2.catch(err => {
    Js.Promise2.resolve({
      Prover.prover: proverId,
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

/** Solve with multiple provers in parallel */
let solveMultiple = (
  config: Prover.proverConfig,
  problem: Prover.problem,
  ~provers: option<array<string>>=?,
): Js.Promise2.t<array<Prover.proverResult>> => {
  let targetProvers = switch provers {
  | Some(ps) => ps
  | None => tptpProvers->Belt.Array.map(p => p.id)
  }

  targetProvers
  ->Belt.Array.map(p => solve(config, problem, ~proverId=p))
  ->Js.Promise2.all
}
