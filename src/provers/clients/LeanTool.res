// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)

/**
 * ECHIDNA LeanTool Client
 * Lean 4 theorem proving via OpenAI-compatible API.
 * Uses the LeanTool OpenAI-compatible API server.
 * Demo: http://www.codeproofarena.com:8800/v1
 */

/** Default LeanTool API endpoint */
let leantoolDefaultEndpoint = "http://www.codeproofarena.com:8800/v1"

/** Lean Playground endpoint for fallback */
let leanPlaygroundUrl = "https://live.lean-lang.org"

/** FFI: Deno.env.get */
@scope(("Deno", "env")) @val
external envGet: string => option<string> = "get"

/** FFI: crypto.randomUUID */
@scope("crypto") @val
external randomUUID: unit => string = "randomUUID"

/** OpenAI-compatible chat completion message */
type chatMessage = {
  role: string,
  content: string,
}

/** OpenAI-compatible chat completion request */
type chatCompletionRequest = {
  model: string,
  messages: array<chatMessage>,
  temperature: option<float>,
  max_tokens: option<int>,
}

/** Chat completion choice */
type chatChoice = {
  index: int,
  message: chatMessage,
  finish_reason: string,
}

/** Token usage stats */
type chatUsage = {
  prompt_tokens: int,
  completion_tokens: int,
  total_tokens: int,
}

/** OpenAI-compatible chat completion response */
type chatCompletionResponse = {
  id: string,
  object: string,
  created: int,
  model: string,
  choices: array<chatChoice>,
  usage: option<chatUsage>,
}

/** Parsed Lean output result */
type parsedLeanOutput = {
  status: Prover.proverStatus,
  proof: option<string>,
  error: option<string>,
}

/** Parse Lean output for proof status */
let parseLeanOutput = (output: string): parsedLeanOutput => {
  let lower = Js.String2.toLowerCase(output)

  // Check for errors
  if (
    Js.String2.includes(lower, "error") ||
    Js.String2.includes(lower, "unknown identifier") ||
    Js.String2.includes(lower, "type mismatch")
  ) {
    {status: Prover.Error, proof: None, error: Some(output)}
  }
  // Check for successful proof
  else if (
    Js.String2.includes(lower, "no goals") ||
    Js.String2.includes(lower, "goals accomplished") ||
    Js.String2.includes(lower, "qed") ||
    Js.String2.includes(lower, "exact") ||
    Js.String2.includes(lower, "rfl")
  ) {
    {status: Prover.Theorem, proof: Some(output), error: None}
  }
  // Check for counterexample
  else if (
    Js.String2.includes(lower, "counterexample") ||
    Js.String2.includes(lower, "failed")
  ) {
    {status: Prover.Countersatisfiable, proof: None, error: Some(output)}
  } else {
    {status: Prover.Unknown, proof: None, error: None}
  }
}

/** LeanTool prover definitions */
let provers: array<Prover.prover> = [
  {
    id: "lean4",
    name: "Lean 4",
    version: None,
    formats: [Prover.Lean],
    endpoint: None,
    tier: 3,
    online: true,
  },
  {
    id: "lean4-mathlib",
    name: "Lean 4 + Mathlib",
    version: None,
    formats: [Prover.Lean],
    endpoint: None,
    tier: 3,
    online: true,
  },
]

/** Client name identifier */
let name = "LeanTool"

/** Make a prover config from partial options */
let makeConfig = (
  ~timeout_sec=120,
  ~retry_count=3,
  ~retry_delay_ms=1000,
  ~api_key=?,
  ~endpoint=?,
  (),
): Prover.proverConfig => {
  timeout_sec,
  retry_count,
  retry_delay_ms,
  api_key,
  endpoint,
}

/** Resolve the endpoint URL from config or environment */
let resolveEndpoint = (config: Prover.proverConfig): string => {
  switch config.endpoint {
  | Some(ep) => ep
  | None =>
    switch envGet("LEANTOOL_ENDPOINT") {
    | Some(ep) => ep
    | None => leantoolDefaultEndpoint
    }
  }
}

/** Resolve the API key from config or environment */
let resolveApiKey = (config: Prover.proverConfig): string => {
  switch config.api_key {
  | Some(k) => k
  | None => Belt.Option.getWithDefault(envGet("LEANTOOL_API_KEY"), "")
  }
}

/** Ping the LeanTool service to check availability */
let ping = (config: Prover.proverConfig): Js.Promise2.t<bool> => {
  let endpoint = resolveEndpoint(config)
  let apiKey = resolveApiKey(config)
  let headers = if Js.String2.length(apiKey) > 0 {
    Some({"Authorization": `Bearer ${apiKey}`})
  } else {
    None
  }
  let url = `${endpoint}/models`

  Http.fetchWithRetry(url, ~init=?headers)
  ->Js.Promise2.then(resp => Js.Promise2.resolve(resp.ok))
  ->Js.Promise2.catch(_ => {
    // Try playground as fallback
    Http.fetchWithRetry(leanPlaygroundUrl)
    ->Js.Promise2.then(resp => Js.Promise2.resolve(resp.ok))
    ->Js.Promise2.catch(_ => Js.Promise2.resolve(false))
  })
}

/** List available provers */
let listProvers = (): Js.Promise2.t<array<Prover.prover>> => {
  Js.Promise2.resolve(provers)
}

/** Solve a problem using the LeanTool API */
let solve = (
  config: Prover.proverConfig,
  problem: Prover.problem,
  ~proverId: string="lean4",
): Js.Promise2.t<Prover.proverResult> => {
  let startTime = Js.Date.now()
  let endpoint = resolveEndpoint(config)
  let apiKey = resolveApiKey(config)

  let model = if proverId == "lean4-mathlib" { "lean4-mathlib" } else { "lean4" }

  let requestBody = Js.Json.object_(Js.Dict.fromArray([
    ("model", Js.Json.string(model)),
    ("messages", Js.Json.array([
      Js.Json.object_(Js.Dict.fromArray([
        ("role", Js.Json.string("system")),
        ("content", Js.Json.string("You are a Lean 4 theorem prover. Verify the given Lean code and report whether it type-checks successfully.")),
      ])),
      Js.Json.object_(Js.Dict.fromArray([
        ("role", Js.Json.string("user")),
        ("content", Js.Json.string(problem.content)),
      ])),
    ])),
    ("temperature", Js.Json.number(0.0)),
    ("max_tokens", Js.Json.number(2048.0)),
  ]))

  let headers = Js.Dict.empty()
  if Js.String2.length(apiKey) > 0 {
    Js.Dict.set(headers, "Authorization", `Bearer ${apiKey}`)
  }

  Http.postJSON(
    `${endpoint}/chat/completions`,
    requestBody,
    ~headers,
    ~options={
      maxRetries: config.retry_count,
      baseDelayMs: config.retry_delay_ms,
      maxDelayMs: 16000,
    },
  )
  ->Js.Promise2.then(json => {
    // Extract output from response choices[0].message.content
    let output = switch Js.Json.decodeObject(json) {
    | Some(obj) =>
      switch Js.Dict.get(obj, "choices") {
      | Some(choices) =>
        switch Js.Json.decodeArray(choices) {
        | Some(arr) if Belt.Array.length(arr) > 0 =>
          switch Js.Json.decodeObject(arr[0]) {
          | Some(choice) =>
            switch Js.Dict.get(choice, "message") {
            | Some(msg) =>
              switch Js.Json.decodeObject(msg) {
              | Some(msgObj) =>
                switch Js.Dict.get(msgObj, "content") {
                | Some(c) => Belt.Option.getWithDefault(Js.Json.decodeString(c), "")
                | None => ""
                }
              | None => ""
              }
            | None => ""
            }
          | None => ""
          }
        | _ => ""
        }
      | None => ""
      }
    | None => ""
    }

    let parsed = parseLeanOutput(output)

    Js.Promise2.resolve({
      Prover.prover: proverId,
      status: parsed.status,
      proof: parsed.proof,
      model: None,
      time_ms: Js.Date.now() -. startTime,
      raw_output: Some(output),
      error: parsed.error,
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

/** Check a Lean theorem (convenience wrapper) */
let checkTheorem = (config: Prover.proverConfig, code: string): Js.Promise2.t<Prover.proverResult> => {
  solve(config, {
    id: randomUUID(),
    name: None,
    format: Prover.Lean,
    content: code,
    expected: None,
    timeout_sec: None,
    metadata: None,
  }, ~proverId="lean4")
}

/** Check with Mathlib imports (convenience wrapper) */
let checkWithMathlib = (config: Prover.proverConfig, code: string): Js.Promise2.t<Prover.proverResult> => {
  solve(config, {
    id: randomUUID(),
    name: None,
    format: Prover.Lean,
    content: code,
    expected: None,
    timeout_sec: None,
    metadata: None,
  }, ~proverId="lean4-mathlib")
}
