// SPDX-License-Identifier: MIT OR Palimpsest-0.6
// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team

/**
 * API client for ECHIDNA Rust backend (v1.3)
 * Connects to HTTP server on port 8080
 */

open Store

// API configuration - connects to Rust backend
let apiBase = "http://localhost:8080/api"

// Session ID tracking (using ref for mutability)
let currentSessionId: ref<option<string>> = ref(None)

// Response types
type apiResponse<'a> = {
  data: option<'a>,
  error: option<string>,
}

// Prover info from backend
type proverInfo = {
  name: string,
  tier: int,
  complexity: int,
}

type proversResponse = {provers: array<proverInfo>}

// JSON decoding helpers using Js.Json
module Decode = {
  let getString = (dict, key) =>
    Belt.Option.flatMap(Js.Dict.get(dict, key), Js.Json.decodeString)

  let getInt = (dict, key) =>
    Belt.Option.flatMap(Js.Dict.get(dict, key), Js.Json.decodeNumber)
    ->Belt.Option.map(Belt.Float.toInt)

  let getFloat = (dict, key) =>
    Belt.Option.flatMap(Js.Dict.get(dict, key), Js.Json.decodeNumber)

  let getBool = (dict, key) =>
    Belt.Option.flatMap(Js.Dict.get(dict, key), Js.Json.decodeBoolean)

  let getArray = (dict, key) =>
    Belt.Option.flatMap(Js.Dict.get(dict, key), Js.Json.decodeArray)

  let goal = (json): option<goal> => {
    Js.Json.decodeObject(json)->Belt.Option.map(dict => {
      {
        id: getString(dict, "id")->Belt.Option.getWithDefault(""),
        hypotheses: getArray(dict, "hypotheses")
          ->Belt.Option.map(arr => Belt.Array.keepMap(arr, Js.Json.decodeString))
          ->Belt.Option.getWithDefault([]),
        conclusion: getString(dict, "conclusion")->Belt.Option.getWithDefault(""),
        context: getArray(dict, "context")
          ->Belt.Option.map(arr => Belt.Array.keepMap(arr, Js.Json.decodeString))
          ->Belt.Option.getWithDefault([]),
      }
    })
  }

  let tacticSuggestion = (json): option<tacticSuggestion> => {
    Js.Json.decodeObject(json)->Belt.Option.map(dict => {
      {
        tactic: getString(dict, "tactic")->Belt.Option.getWithDefault(""),
        confidence: getFloat(dict, "confidence")->Belt.Option.getWithDefault(0.0),
        premise: getString(dict, "premise"),
        aspectTags: getArray(dict, "aspect_tags")
          ->Belt.Option.map(arr => Belt.Array.keepMap(arr, Js.Json.decodeString))
          ->Belt.Option.getWithDefault([]),
      }
    })
  }

  let proofState = (json): option<proofState> => {
    Js.Json.decodeObject(json)->Belt.Option.map(dict => {
      {
        goals: getArray(dict, "goals")
          ->Belt.Option.map(arr => Belt.Array.keepMap(arr, goal))
          ->Belt.Option.getWithDefault([]),
        currentGoalIndex: getInt(dict, "current_goal_index")->Belt.Option.getWithDefault(0),
        proofScript: getArray(dict, "proof_script")
          ->Belt.Option.map(arr => Belt.Array.keepMap(arr, Js.Json.decodeString))
          ->Belt.Option.getWithDefault([]),
        completed: getBool(dict, "completed")->Belt.Option.getWithDefault(false),
      }
    })
  }

  let aspectTag = (json): option<aspectTag> => {
    Js.Json.decodeObject(json)->Belt.Option.map(dict => {
      {
        name: getString(dict, "name")->Belt.Option.getWithDefault(""),
        category: getString(dict, "category")->Belt.Option.getWithDefault(""),
        active: getBool(dict, "active")->Belt.Option.getWithDefault(false),
      }
    })
  }

  let proverInfo = (json): option<proverInfo> => {
    Js.Json.decodeObject(json)->Belt.Option.map(dict => {
      {
        name: getString(dict, "name")->Belt.Option.getWithDefault(""),
        tier: getInt(dict, "tier")->Belt.Option.getWithDefault(0),
        complexity: getInt(dict, "complexity")->Belt.Option.getWithDefault(0),
      }
    })
  }
}

module Encode = {
  let createSessionRequest = (prover: prover): Js.Json.t => {
    let dict = Js.Dict.empty()
    Js.Dict.set(dict, "prover", Js.Json.string(proverToString(prover)))
    Js.Dict.set(dict, "goal", Js.Json.string(""))
    Js.Json.object_(dict)
  }

  let applyTacticRequest = (tactic: string): Js.Json.t => {
    let dict = Js.Dict.empty()
    Js.Dict.set(dict, "tactic", Js.Json.string(tactic))
    Js.Json.object_(dict)
  }

  let searchQuery = (query: string): Js.Json.t => {
    let dict = Js.Dict.empty()
    Js.Dict.set(dict, "q", Js.Json.string(query))
    Js.Json.object_(dict)
  }
}

// API helper functions
let handleResponse = (response: Webapi.Fetch.Response.t): promise<apiResponse<Js.Json.t>> => {
  if response->Webapi.Fetch.Response.ok {
    response->Webapi.Fetch.Response.json
    |> Js.Promise.then_(json => Js.Promise.resolve({data: Some(json), error: None}))
    |> Js.Promise.catch(_ => Js.Promise.resolve({
      data: None,
      error: Some("Failed to parse response"),
    }))
  } else {
    let status = response->Webapi.Fetch.Response.status
    Js.Promise.resolve({
      data: None,
      error: Some(`API error: ${Belt.Int.toString(status)}`),
    })
  }
}

// Get available provers
let getProvers = (): promise<result<array<proverInfo>, string>> => {
  Webapi.Fetch.fetch(`${apiBase}/provers`)
  |> Js.Promise.then_(handleResponse)
  |> Js.Promise.then_(result => {
    switch result {
    | {data: Some(json), error: None} =>
      switch Js.Json.decodeObject(json) {
      | Some(dict) =>
        switch Js.Dict.get(dict, "provers") {
        | Some(proversJson) =>
          switch Js.Json.decodeArray(proversJson) {
          | Some(arr) =>
            let provers = Belt.Array.keepMap(arr, Decode.proverInfo)
            Js.Promise.resolve(Ok(provers))
          | None => Js.Promise.resolve(Error("Failed to decode provers array"))
          }
        | None => Js.Promise.resolve(Error("Missing 'provers' field"))
        }
      | None => Js.Promise.resolve(Error("Invalid JSON response"))
      }
    | {error: Some(err)} => Js.Promise.resolve(Error(err))
    | _ => Js.Promise.resolve(Error("Unknown error"))
    }
  })
  |> Js.Promise.catch(_ => Js.Promise.resolve(Error("Network error")))
}

// Initialize proof session (creates new session)
let initProofSession = (prover: prover): promise<result<proofState, string>> => {
  let init = Webapi.Fetch.RequestInit.make(
    ~method_=Post,
    ~body=Webapi.Fetch.BodyInit.make(Encode.createSessionRequest(prover)->Js.Json.stringify),
    ~headers=Webapi.Fetch.HeadersInit.make({"Content-Type": "application/json"}),
    (),
  )

  Webapi.Fetch.fetchWithInit(`${apiBase}/session/create`, init)
  |> Js.Promise.then_(handleResponse)
  |> Js.Promise.then_(result => {
    switch result {
    | {data: Some(json), error: None} =>
      switch Js.Json.decodeObject(json) {
      | Some(dict) =>
        switch Decode.getString(dict, "session_id") {
        | Some(sessionId) =>
          currentSessionId := Some(sessionId)
          switch Js.Dict.get(dict, "state") {
          | Some(stateJson) =>
            switch Decode.proofState(stateJson) {
            | Some(state) => Js.Promise.resolve(Ok(state))
            | None => Js.Promise.resolve(Error("Failed to decode proof state"))
            }
          | None => Js.Promise.resolve(Error("Missing 'state' field"))
          }
        | None => Js.Promise.resolve(Error("Missing 'session_id' field"))
        }
      | None => Js.Promise.resolve(Error("Invalid JSON response"))
      }
    | {error: Some(err)} => Js.Promise.resolve(Error(err))
    | _ => Js.Promise.resolve(Error("Unknown error"))
    }
  })
  |> Js.Promise.catch(_ => Js.Promise.resolve(Error("Network error")))
}

// Apply tactic to current session
let applyTactic = (tactic: string, _goalId: string): promise<result<proofState, string>> => {
  switch currentSessionId.contents {
  | None => Js.Promise.resolve(Error("No active session"))
  | Some(sessionId) =>
    let init = Webapi.Fetch.RequestInit.make(
      ~method_=Post,
      ~body=Webapi.Fetch.BodyInit.make(Encode.applyTacticRequest(tactic)->Js.Json.stringify),
      ~headers=Webapi.Fetch.HeadersInit.make({"Content-Type": "application/json"}),
      (),
    )

    Webapi.Fetch.fetchWithInit(`${apiBase}/session/${sessionId}/apply`, init)
    |> Js.Promise.then_(handleResponse)
    |> Js.Promise.then_(result => {
      switch result {
      | {data: Some(json), error: None} =>
        switch Js.Json.decodeObject(json) {
        | Some(dict) =>
          switch Js.Dict.get(dict, "state") {
          | Some(stateJson) =>
            switch Decode.proofState(stateJson) {
            | Some(state) => Js.Promise.resolve(Ok(state))
            | None => Js.Promise.resolve(Error("Failed to decode proof state"))
            }
          | None => Js.Promise.resolve(Error("Missing 'state' field"))
          }
        | None => Js.Promise.resolve(Error("Invalid JSON response"))
        }
      | {error: Some(err)} => Js.Promise.resolve(Error(err))
      | _ => Js.Promise.resolve(Error("Unknown error"))
      }
    })
    |> Js.Promise.catch(_ => Js.Promise.resolve(Error("Network error")))
  }
}

// Get tactic suggestions (neural)
let getTacticSuggestions = (
  _goalId: string,
  _aspectTags: array<string>,
): promise<result<array<tacticSuggestion>, string>> => {
  switch currentSessionId.contents {
  | None => Js.Promise.resolve(Error("No active session"))
  | Some(_sessionId) =>
    let init = Webapi.Fetch.RequestInit.make(
      ~method_=Post,
      ~body=Webapi.Fetch.BodyInit.make("{}"),
      ~headers=Webapi.Fetch.HeadersInit.make({"Content-Type": "application/json"}),
      (),
    )

    Webapi.Fetch.fetchWithInit(`${apiBase}/suggest`, init)
    |> Js.Promise.then_(handleResponse)
    |> Js.Promise.then_(result => {
      switch result {
      | {data: Some(json), error: None} =>
        switch Js.Json.decodeObject(json) {
        | Some(dict) =>
          switch Js.Dict.get(dict, "suggestions") {
          | Some(suggestionsJson) =>
            switch Js.Json.decodeArray(suggestionsJson) {
            | Some(arr) =>
              let suggestions = Belt.Array.keepMap(arr, Decode.tacticSuggestion)
              Js.Promise.resolve(Ok(suggestions))
            | None => Js.Promise.resolve(Error("Failed to decode suggestions array"))
            }
          | None => Js.Promise.resolve(Error("Missing 'suggestions' field"))
          }
        | None => Js.Promise.resolve(Error("Invalid JSON response"))
        }
      | {error: Some(err)} => Js.Promise.resolve(Error(err))
      | _ => Js.Promise.resolve(Error("Unknown error"))
      }
    })
    |> Js.Promise.catch(_ => Js.Promise.resolve(Error("Network error")))
  }
}

// Search theorems
let searchTheorems = (query: string, _aspectTags: array<string>): promise<
  result<array<string>, string>,
> => {
  let url = `${apiBase}/search?q=${query}`

  Webapi.Fetch.fetch(url)
  |> Js.Promise.then_(handleResponse)
  |> Js.Promise.then_(result => {
    switch result {
    | {data: Some(json), error: None} =>
      switch Js.Json.decodeObject(json) {
      | Some(dict) =>
        switch Js.Dict.get(dict, "results") {
        | Some(resultsJson) =>
          switch Js.Json.decodeArray(resultsJson) {
          | Some(arr) =>
            let theorems = Belt.Array.keepMap(arr, Js.Json.decodeString)
            Js.Promise.resolve(Ok(theorems))
          | None => Js.Promise.resolve(Error("Failed to decode results array"))
          }
        | None => Js.Promise.resolve(Error("Missing 'results' field"))
        }
      | None => Js.Promise.resolve(Error("Invalid JSON response"))
      }
    | {error: Some(err)} => Js.Promise.resolve(Error(err))
    | _ => Js.Promise.resolve(Error("Unknown error"))
    }
  })
  |> Js.Promise.catch(_ => Js.Promise.resolve(Error("Network error")))
}

// Get aspect tags (mock for now - not yet implemented in backend)
let getAspectTags = (): promise<result<array<aspectTag>, string>> => {
  // Return mock data until backend implements this
  let mockTags = [
    {name: "constructive", category: "logic", active: false},
    {name: "computational", category: "type", active: false},
    {name: "algebraic", category: "domain", active: false},
  ]
  Js.Promise.resolve(Ok(mockTags))
}

// Get proof tree structure (mock for now)
let getProofTree = (): promise<result<Js.Json.t, string>> => {
  // Return empty tree until backend implements this
  Js.Promise.resolve(Ok(Js.Json.object_(Js.Dict.empty())))
}

// Health check
let checkHealth = (): promise<result<bool, string>> => {
  Webapi.Fetch.fetch(`${apiBase}/health`)
  |> Js.Promise.then_(response => {
    if response->Webapi.Fetch.Response.ok {
      Js.Promise.resolve(Ok(true))
    } else {
      Js.Promise.resolve(Error("Backend not healthy"))
    }
  })
  |> Js.Promise.catch(_ => Js.Promise.resolve(Error("Network error")))
}
