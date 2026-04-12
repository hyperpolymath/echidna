// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team

/**
 * API client for ECHIDNA Rust backend (v1.3)
 * Connects to HTTP server on port 8081
 */

open Store

// API configuration - connects to Rust backend
let apiBase = "http://localhost:8081/api"

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

// JSON decoding helpers using RescriptCore JSON
module Decode = {
  let getString = (dict, key) =>
    dict->Dict.get(key)->Belt.Option.flatMap(JSON.Decode.string)

  let getInt = (dict, key) =>
    dict->Dict.get(key)
    ->Belt.Option.flatMap(JSON.Decode.float)
    ->Belt.Option.map(Belt.Float.toInt)

  let getFloat = (dict, key) =>
    dict->Dict.get(key)->Belt.Option.flatMap(JSON.Decode.float)

  let getBool = (dict, key) =>
    dict->Dict.get(key)->Belt.Option.flatMap(JSON.Decode.bool)

  let getArray = (dict, key) =>
    dict->Dict.get(key)->Belt.Option.flatMap(JSON.Decode.array)

  let goal = (json): option<goal> => {
    json->JSON.Decode.object->Belt.Option.map(dict => {
      {
        id: getString(dict, "id")->Belt.Option.getWithDefault(""),
        hypotheses: getArray(dict, "hypotheses")
          ->Belt.Option.map(arr => arr->Belt.Array.keepMap(JSON.Decode.string))
          ->Belt.Option.getWithDefault([]),
        conclusion: getString(dict, "conclusion")->Belt.Option.getWithDefault(""),
        context: getArray(dict, "context")
          ->Belt.Option.map(arr => arr->Belt.Array.keepMap(JSON.Decode.string))
          ->Belt.Option.getWithDefault([]),
      }
    })
  }

  let tacticSuggestion = (json): option<tacticSuggestion> => {
    json->JSON.Decode.object->Belt.Option.map(dict => {
      {
        tactic: getString(dict, "tactic")->Belt.Option.getWithDefault(""),
        confidence: getFloat(dict, "confidence")->Belt.Option.getWithDefault(0.0),
        premise: getString(dict, "premise"),
        aspectTags: getArray(dict, "aspect_tags")
          ->Belt.Option.map(arr => arr->Belt.Array.keepMap(JSON.Decode.string))
          ->Belt.Option.getWithDefault([]),
      }
    })
  }

  let proofState = (json): option<proofState> => {
    json->JSON.Decode.object->Belt.Option.map(dict => {
      {
        goals: getArray(dict, "goals")
          ->Belt.Option.map(arr => arr->Belt.Array.keepMap(goal))
          ->Belt.Option.getWithDefault([]),
        currentGoalIndex: getInt(dict, "current_goal_index")->Belt.Option.getWithDefault(0),
        proofScript: getArray(dict, "proof_script")
          ->Belt.Option.map(arr => arr->Belt.Array.keepMap(JSON.Decode.string))
          ->Belt.Option.getWithDefault([]),
        completed: getBool(dict, "completed")->Belt.Option.getWithDefault(false),
      }
    })
  }

  let aspectTag = (json): option<aspectTag> => {
    json->JSON.Decode.object->Belt.Option.map(dict => {
      {
        name: getString(dict, "name")->Belt.Option.getWithDefault(""),
        category: getString(dict, "category")->Belt.Option.getWithDefault(""),
        active: getBool(dict, "active")->Belt.Option.getWithDefault(false),
      }
    })
  }

  let proverInfo = (json): option<proverInfo> => {
    json->JSON.Decode.object->Belt.Option.map(dict => {
      {
        name: getString(dict, "name")->Belt.Option.getWithDefault(""),
        tier: getInt(dict, "tier")->Belt.Option.getWithDefault(0),
        complexity: getInt(dict, "complexity")->Belt.Option.getWithDefault(0),
      }
    })
  }
}

module Encode = {
  let createSessionRequest = (prover: prover): JSON.t => {
    let dict = Dict.make()
    dict->Dict.set("prover", JSON.Encode.string(proverToString(prover)))
    dict->Dict.set("goal", JSON.Encode.string(""))
    JSON.Encode.object(dict)
  }

  let applyTacticRequest = (tactic: string): JSON.t => {
    let dict = Dict.make()
    dict->Dict.set("tactic", JSON.Encode.string(tactic))
    JSON.Encode.object(dict)
  }

  let searchQuery = (query: string): JSON.t => {
    let dict = Dict.make()
    dict->Dict.set("q", JSON.Encode.string(query))
    JSON.Encode.object(dict)
  }
}

// API helper functions
let handleResponse = (response: Webapi.Fetch.Response.t): promise<apiResponse<JSON.t>> => {
  if response->Webapi.Fetch.Response.ok {
    response->Webapi.Fetch.Response.json
    ->Promise.then(json => Promise.resolve({data: Some(json), error: None}))
    ->Promise.catch(_ => Promise.resolve({
      data: None,
      error: Some("Failed to parse response"),
    }))
  } else {
    let status = response->Webapi.Fetch.Response.status
    Promise.resolve({
      data: None,
      error: Some(`API error: ${Belt.Int.toString(status)}`),
    })
  }
}

// Get available provers
let getProvers = (): promise<result<array<proverInfo>, string>> => {
  Webapi.Fetch.fetch(`${apiBase}/provers`)
  ->Promise.then(handleResponse)
  ->Promise.then(result => {
    switch result {
    | {data: Some(json), error: None} =>
      switch json->JSON.Decode.object {
      | Some(dict) =>
        switch dict->Dict.get("provers") {
        | Some(proversJson) =>
          switch proversJson->JSON.Decode.array {
          | Some(arr) =>
            let provers = arr->Belt.Array.keepMap(Decode.proverInfo)
            Promise.resolve(Ok(provers))
          | None => Promise.resolve(Error("Failed to decode provers array"))
          }
        | None => Promise.resolve(Error("Missing 'provers' field"))
        }
      | None => Promise.resolve(Error("Invalid JSON response"))
      }
    | {error: Some(err)} => Promise.resolve(Error(err))
    | _ => Promise.resolve(Error("Unknown error"))
    }
  })
  ->Promise.catch(_ => Promise.resolve(Error("Network error")))
}

// Initialize proof session (creates new session)
let initProofSession = (prover: prover): promise<result<proofState, string>> => {
  let init = Webapi.Fetch.RequestInit.make(
    ~method_=Post,
    ~body=Webapi.Fetch.BodyInit.make(Encode.createSessionRequest(prover)->JSON.stringify),
    ~headers=Webapi.Fetch.HeadersInit.make({"Content-Type": "application/json"}),
    (),
  )

  Webapi.Fetch.fetchWithInit(`${apiBase}/session/create`, init)
  ->Promise.then(handleResponse)
  ->Promise.then(result => {
    switch result {
    | {data: Some(json), error: None} =>
      switch json->JSON.Decode.object {
      | Some(dict) =>
        switch Decode.getString(dict, "session_id") {
        | Some(sessionId) =>
          currentSessionId := Some(sessionId)
          switch dict->Dict.get("state") {
          | Some(stateJson) =>
            switch Decode.proofState(stateJson) {
            | Some(state) => Promise.resolve(Ok(state))
            | None => Promise.resolve(Error("Failed to decode proof state"))
            }
          | None => Promise.resolve(Error("Missing 'state' field"))
          }
        | None => Promise.resolve(Error("Missing 'session_id' field"))
        }
      | None => Promise.resolve(Error("Invalid JSON response"))
      }
    | {error: Some(err)} => Promise.resolve(Error(err))
    | _ => Promise.resolve(Error("Unknown error"))
    }
  })
  ->Promise.catch(_ => Promise.resolve(Error("Network error")))
}

// Apply tactic to current session
let applyTactic = (tactic: string, _goalId: string): promise<result<proofState, string>> => {
  switch currentSessionId.contents {
  | None => Promise.resolve(Error("No active session"))
  | Some(sessionId) =>
    let init = Webapi.Fetch.RequestInit.make(
      ~method_=Post,
      ~body=Webapi.Fetch.BodyInit.make(Encode.applyTacticRequest(tactic)->JSON.stringify),
      ~headers=Webapi.Fetch.HeadersInit.make({"Content-Type": "application/json"}),
      (),
    )

    Webapi.Fetch.fetchWithInit(`${apiBase}/session/${sessionId}/apply`, init)
    ->Promise.then(handleResponse)
    ->Promise.then(result => {
      switch result {
      | {data: Some(json), error: None} =>
        switch json->JSON.Decode.object {
        | Some(dict) =>
          switch dict->Dict.get("state") {
          | Some(stateJson) =>
            switch Decode.proofState(stateJson) {
            | Some(state) => Promise.resolve(Ok(state))
            | None => Promise.resolve(Error("Failed to decode proof state"))
            }
          | None => Promise.resolve(Error("Missing 'state' field"))
          }
        | None => Promise.resolve(Error("Invalid JSON response"))
        }
      | {error: Some(err)} => Promise.resolve(Error(err))
      | _ => Promise.resolve(Error("Unknown error"))
      }
    })
    ->Promise.catch(_ => Promise.resolve(Error("Network error")))
  }
}

// Get tactic suggestions (neural)
let getTacticSuggestions = (
  _goalId: string,
  _aspectTags: array<string>,
): promise<result<array<tacticSuggestion>, string>> => {
  switch currentSessionId.contents {
  | None => Promise.resolve(Error("No active session"))
  | Some(_sessionId) =>
    let init = Webapi.Fetch.RequestInit.make(
      ~method_=Post,
      ~body=Webapi.Fetch.BodyInit.make("{}"),
      ~headers=Webapi.Fetch.HeadersInit.make({"Content-Type": "application/json"}),
      (),
    )

    Webapi.Fetch.fetchWithInit(`${apiBase}/suggest`, init)
    ->Promise.then(handleResponse)
    ->Promise.then(result => {
      switch result {
      | {data: Some(json), error: None} =>
        switch json->JSON.Decode.object {
        | Some(dict) =>
          switch dict->Dict.get("suggestions") {
          | Some(suggestionsJson) =>
            switch suggestionsJson->JSON.Decode.array {
            | Some(arr) =>
              let suggestions = arr->Belt.Array.keepMap(Decode.tacticSuggestion)
              Promise.resolve(Ok(suggestions))
            | None => Promise.resolve(Error("Failed to decode suggestions array"))
            }
          | None => Promise.resolve(Error("Missing 'suggestions' field"))
          }
        | None => Promise.resolve(Error("Invalid JSON response"))
        }
      | {error: Some(err)} => Promise.resolve(Error(err))
      | _ => Promise.resolve(Error("Unknown error"))
      }
    })
    ->Promise.catch(_ => Promise.resolve(Error("Network error")))
  }
}

// Search theorems
let searchTheorems = (query: string, _aspectTags: array<string>): promise<
  result<array<string>, string>,
> => {
  let url = `${apiBase}/search?q=${query}`

  Webapi.Fetch.fetch(url)
  ->Promise.then(handleResponse)
  ->Promise.then(result => {
    switch result {
    | {data: Some(json), error: None} =>
      switch json->JSON.Decode.object {
      | Some(dict) =>
        switch dict->Dict.get("results") {
        | Some(resultsJson) =>
          switch resultsJson->JSON.Decode.array {
          | Some(arr) =>
            let theorems = arr->Belt.Array.keepMap(JSON.Decode.string)
            Promise.resolve(Ok(theorems))
          | None => Promise.resolve(Error("Failed to decode results array"))
          }
        | None => Promise.resolve(Error("Missing 'results' field"))
        }
      | None => Promise.resolve(Error("Invalid JSON response"))
      }
    | {error: Some(err)} => Promise.resolve(Error(err))
    | _ => Promise.resolve(Error("Unknown error"))
    }
  })
  ->Promise.catch(_ => Promise.resolve(Error("Network error")))
}

// Get aspect tags (mock for now - not yet implemented in backend)
let getAspectTags = (): promise<result<array<aspectTag>, string>> => {
  // Return mock data until backend implements this
  let mockTags = [
    {name: "constructive", category: "logic", active: false},
    {name: "computational", category: "type", active: false},
    {name: "algebraic", category: "domain", active: false},
  ]
  Promise.resolve(Ok(mockTags))
}

// Get proof tree structure (mock for now)
let getProofTree = (): promise<result<JSON.t, string>> => {
  // Return empty tree until backend implements this
  Promise.resolve(Ok(JSON.Encode.object(Dict.make())))
}

// Health check
let checkHealth = (): promise<result<bool, string>> => {
  Webapi.Fetch.fetch(`${apiBase}/health`)
  ->Promise.then(response => {
    if response->Webapi.Fetch.Response.ok {
      Promise.resolve(Ok(true))
    } else {
      Promise.resolve(Error("Backend not healthy"))
    }
  })
  ->Promise.catch(_ => Promise.resolve(Error("Network error")))
}
