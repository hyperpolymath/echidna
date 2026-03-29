// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)

/**
 * ECHIDNA Wolfram Alpha API Client
 * Theorem proving and equation solving via Wolfram Alpha.
 * Free tier: 2,000 non-commercial API calls per month.
 * Get API key at: https://developer.wolframalpha.com/
 */

/** Wolfram Alpha API base URL */
let wolframApiBase = "https://api.wolframalpha.com/v2"

/** FFI: Deno.env.get */
@scope(("Deno", "env")) @val
external envGet: string => option<string> = "get"

/** FFI: crypto.randomUUID */
@scope("crypto") @val
external randomUUID: unit => string = "randomUUID"

/** Wolfram subpod image */
type wolframImage = {
  src: string,
  alt: string,
}

/** Wolfram subpod */
type wolframSubpod = {
  title: string,
  plaintext: option<string>,
  img: option<wolframImage>,
}

/** Wolfram pod */
type wolframPod = {
  title: string,
  id: string,
  primary: option<bool>,
  subpods: array<wolframSubpod>,
}

/** Wolfram query result */
type wolframQueryResult = {
  success: bool,
  error: bool,
  numpods: int,
  pods: option<array<wolframPod>>,
  timedout: string,
  timing: float,
}

/** Wolfram API response */
type wolframResponse = {
  queryresult: wolframQueryResult,
}

/** Proof extraction result */
type proofContent = {
  status: Prover.proverStatus,
  proof: option<string>,
  model: option<string>,
}

/** Extract proof-related content from Wolfram response */
let extractProofContent = (pods: array<wolframPod>): proofContent => {
  let findPod = (keywords: array<string>): option<wolframPod> => {
    pods->Belt.Array.getBy(p => {
      let lower = Js.String2.toLowerCase(p.title)
      keywords->Belt.Array.some(kw => Js.String2.includes(lower, kw))
    })
  }

  let proofPod = findPod(["proof", "derivation", "step"])
  let resultPod = switch pods->Belt.Array.getBy(p => {
    let lower = Js.String2.toLowerCase(p.title)
    Js.String2.includes(lower, "result") ||
    Js.String2.includes(lower, "solution") ||
    Belt.Option.getWithDefault(p.primary, false)
  }) {
  | Some(p) => Some(p)
  | None => None
  }
  let truthPod = findPod(["truth", "statement"])

  let status = ref(Prover.Unknown)
  let proof = ref(None)
  let model = ref(None)

  switch proofPod {
  | Some(pod) => {
      proof := Some(
        pod.subpods
        ->Belt.Array.keepMap(s => s.plaintext)
        ->Js.Array2.joinWith("\n")
      )
      status := Prover.Theorem
    }
  | None => ()
  }

  switch truthPod {
  | Some(pod) =>
    switch Belt.Array.get(pod.subpods, 0) {
    | Some(sub) =>
      switch sub.plaintext {
      | Some(text) => {
          let lower = Js.String2.toLowerCase(text)
          if Js.String2.includes(lower, "true") || Js.String2.includes(lower, "valid") {
            status := Prover.Theorem
          } else if Js.String2.includes(lower, "false") || Js.String2.includes(lower, "invalid") {
            status := Prover.Countersatisfiable
          }
        }
      | None => ()
      }
    | None => ()
    }
  | None => ()
  }

  switch resultPod {
  | Some(pod) => {
      let modelText = pod.subpods
        ->Belt.Array.keepMap(s => s.plaintext)
        ->Js.Array2.joinWith("\n")
      if Js.String2.length(modelText) > 0 {
        model := Some(modelText)
        if status.contents == Prover.Unknown {
          status := Prover.Satisfiable
        }
      }
    }
  | None => ()
  }

  {
    status: status.contents,
    proof: proof.contents,
    model: model.contents,
  }
}

/** Client name identifier */
let name = "WolframAlpha"

/** Prover definitions for this client */
let provers: array<Prover.prover> = [
  {
    id: "wolfram-prove",
    name: "Wolfram Alpha Prover",
    version: None,
    formats: [Prover.Natural, Prover.Wolfram],
    endpoint: None,
    tier: 3,
    online: true,
  },
  {
    id: "wolfram-solve",
    name: "Wolfram Alpha Solver",
    version: None,
    formats: [Prover.Natural, Prover.Wolfram],
    endpoint: None,
    tier: 3,
    online: true,
  },
]

/** Resolve API key from config or environment */
let resolveApiKey = (config: Prover.proverConfig): string => {
  switch config.api_key {
  | Some(k) => k
  | None => Belt.Option.getWithDefault(envGet("WOLFRAM_APP_ID"), "")
  }
}

/** Ping the Wolfram Alpha service */
let ping = (config: Prover.proverConfig): Js.Promise2.t<bool> => {
  let apiKey = resolveApiKey(config)
  if Js.String2.length(apiKey) == 0 {
    Js.log("[Wolfram] No API key configured (set WOLFRAM_APP_ID)")
    Js.Promise2.resolve(false)
  } else {
    let url = `${wolframApiBase}/query?appid=${apiKey}&input=2%2B2&format=plaintext&output=json`
    Http.fetchWithRetry(url)
    ->Js.Promise2.then(resp => Http.responseJson(resp))
    ->Js.Promise2.then(_data => Js.Promise2.resolve(true))
    ->Js.Promise2.catch(_ => Js.Promise2.resolve(false))
  }
}

/** List available provers */
let listProvers = (): Js.Promise2.t<array<Prover.prover>> => {
  Js.Promise2.resolve(provers)
}

/** Solve a problem using Wolfram Alpha */
let solve = (
  config: Prover.proverConfig,
  problem: Prover.problem,
  ~proverId: string="wolfram-prove",
): Js.Promise2.t<Prover.proverResult> => {
  let startTime = Js.Date.now()
  let apiKey = resolveApiKey(config)

  if Js.String2.length(apiKey) == 0 {
    Js.Promise2.resolve({
      Prover.prover: proverId,
      status: Prover.Error,
      proof: None,
      model: None,
      time_ms: Js.Date.now() -. startTime,
      raw_output: None,
      error: Some("No Wolfram Alpha API key configured. Set WOLFRAM_APP_ID environment variable."),
      timestamp: Js.Date.make(),
    })
  } else {
    let query = if proverId == "wolfram-prove" {
      let lower = Js.String2.toLowerCase(problem.content)
      if !Js.String2.startsWith(lower, "prove") {
        `prove ${problem.content}`
      } else {
        problem.content
      }
    } else {
      problem.content
    }

    let timeout = Belt.Option.getWithDefault(problem.timeout_sec, config.timeout_sec)
    let encodedQuery = Js.Global.encodeURIComponent(query)
    let url = `${wolframApiBase}/query?appid=${apiKey}&input=${encodedQuery}&format=plaintext&output=json&podtimeout=${Belt.Int.toString(timeout)}`

    Http.fetchWithRetry(url, ~options={
      maxRetries: config.retry_count,
      baseDelayMs: config.retry_delay_ms,
      maxDelayMs: 16000,
    })
    ->Js.Promise2.then(resp => Http.responseJson(resp))
    ->Js.Promise2.then(data => {
      // Parse the Wolfram response from JSON
      // Note: In production, use a proper JSON decoder
      let status = Prover.Unknown
      let _ = data

      Js.Promise2.resolve({
        Prover.prover: proverId,
        status,
        proof: None,
        model: None,
        time_ms: Js.Date.now() -. startTime,
        raw_output: Some(Js.Json.stringify(data)),
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
}

/** Prove a mathematical statement (convenience wrapper) */
let prove = (config: Prover.proverConfig, statement: string): Js.Promise2.t<Prover.proverResult> => {
  solve(config, {
    id: randomUUID(),
    name: None,
    format: Prover.Natural,
    content: statement,
    expected: None,
    timeout_sec: None,
    metadata: None,
  }, ~proverId="wolfram-prove")
}

/** Solve an equation or system (convenience wrapper) */
let equation = (config: Prover.proverConfig, eq: string): Js.Promise2.t<Prover.proverResult> => {
  solve(config, {
    id: randomUUID(),
    name: None,
    format: Prover.Natural,
    content: `solve ${eq}`,
    expected: None,
    timeout_sec: None,
    metadata: None,
  }, ~proverId="wolfram-solve")
}
