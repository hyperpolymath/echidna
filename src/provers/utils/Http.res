// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)

/**
 * ECHIDNA HTTP Utilities
 * Deno-native HTTP client utilities with retry logic
 */

/** Retry configuration options */
type retryOptions = {
  maxRetries: int,
  baseDelayMs: int,
  maxDelayMs: int,
}

/** Default retry configuration */
let defaultRetry: retryOptions = {
  maxRetries: 3,
  baseDelayMs: 1000,
  maxDelayMs: 16000,
}

/** FFI bindings to global fetch and related APIs */
@val external fetch: (string, 'a) => Js.Promise2.t<'b> = "fetch"
@val external fetchUrl: string => Js.Promise2.t<'a> = "fetch"
@val external setTimeout: (unit => unit, int) => int = "setTimeout"

/** Response type from fetch API */
type response = {
  ok: bool,
  status: int,
  statusText: string,
}

@send external responseText: response => Js.Promise2.t<string> = "text"
@send external responseJson: response => Js.Promise2.t<Js.Json.t> = "json"

/** Sleep for specified milliseconds */
let sleep = (ms: int): Js.Promise2.t<unit> => {
  Js.Promise2.make((~resolve, ~reject as _reject) => {
    let _ = setTimeout(() => resolve(), ms)
  })
}

/** Calculate exponential backoff delay */
let backoffDelay = (attempt: int, options: retryOptions): int => {
  let delay = options.baseDelayMs * Js.Math.pow_int(~base=2, ~exp=attempt)
  Js.Math.min_int(delay, options.maxDelayMs)
}

/** Fetch with exponential backoff retry.
 * Returns a promise that resolves to the Response object.
 * Retries on server errors (status >= 500) and network failures.
 */
let fetchWithRetry = (
  url: string,
  ~init: option<{..}>=?,
  ~options: retryOptions=defaultRetry,
): Js.Promise2.t<response> => {
  let rec attempt = (n: int, lastError: option<string>): Js.Promise2.t<response> => {
    if n > options.maxRetries {
      Js.Promise2.reject(
        Js.Exn.raiseError(`Failed after ${Belt.Int.toString(options.maxRetries)} retries: ${Belt.Option.getWithDefault(lastError, "unknown error")}`)
      )
    } else {
      let fetchPromise = switch init {
      | Some(i) => fetch(url, i)
      | None => fetchUrl(url)
      }
      fetchPromise
      ->Js.Promise2.then(resp => {
        if resp.status >= 500 && n < options.maxRetries {
          sleep(backoffDelay(n, options))
          ->Js.Promise2.then(_ => attempt(n + 1, Some(`HTTP ${Belt.Int.toString(resp.status)}`)))
        } else {
          Js.Promise2.resolve(resp)
        }
      })
      ->Js.Promise2.catch(err => {
        let errMsg = Js.String.make(err)
        if n < options.maxRetries {
          Js.log(`[HTTP] Retry ${Belt.Int.toString(n + 1)}/${Belt.Int.toString(options.maxRetries)} for ${url}: ${errMsg}`)
          sleep(backoffDelay(n, options))
          ->Js.Promise2.then(_ => attempt(n + 1, Some(errMsg)))
        } else {
          Js.Promise2.reject(
            Js.Exn.raiseError(`Failed after ${Belt.Int.toString(options.maxRetries)} retries: ${errMsg}`)
          )
        }
      })
    }
  }
  attempt(0, None)
}

/** POST form data (for SystemOnTPTP) */
let postForm = (
  url: string,
  data: Js.Dict.t<string>,
  ~options: retryOptions=defaultRetry,
): Js.Promise2.t<string> => {
  let params = Js.Dict.entries(data)
    ->Belt.Array.map(((k, v)) => `${k}=${v}`)
    ->Js.Array2.joinWith("&")

  fetchWithRetry(url, ~init=Some({
    "method": "POST",
    "headers": {"Content-Type": "application/x-www-form-urlencoded"},
    "body": params,
  }), ~options)
  ->Js.Promise2.then(resp => {
    if !resp.ok {
      Js.Promise2.reject(
        Js.Exn.raiseError(`HTTP ${Belt.Int.toString(resp.status)}: ${resp.statusText}`)
      )
    } else {
      responseText(resp)
    }
  })
}

/** POST JSON and parse response */
let postJSON = (
  url: string,
  data: Js.Json.t,
  ~headers: Js.Dict.t<string>=Js.Dict.empty(),
  ~options: retryOptions=defaultRetry,
): Js.Promise2.t<Js.Json.t> => {
  let allHeaders = Js.Dict.fromArray([("Content-Type", "application/json")])
  Js.Dict.entries(headers)->Belt.Array.forEach(((k, v)) => Js.Dict.set(allHeaders, k, v))

  fetchWithRetry(url, ~init=Some({
    "method": "POST",
    "headers": allHeaders,
    "body": Js.Json.stringify(data),
  }), ~options)
  ->Js.Promise2.then(resp => {
    if !resp.ok {
      Js.Promise2.reject(
        Js.Exn.raiseError(`HTTP ${Belt.Int.toString(resp.status)}: ${resp.statusText}`)
      )
    } else {
      responseJson(resp)
    }
  })
}

/** GET request returning text body */
let getText = (
  url: string,
  ~options: retryOptions=defaultRetry,
): Js.Promise2.t<string> => {
  fetchWithRetry(url, ~options)
  ->Js.Promise2.then(resp => {
    if !resp.ok {
      Js.Promise2.reject(
        Js.Exn.raiseError(`HTTP ${Belt.Int.toString(resp.status)}: ${resp.statusText}`)
      )
    } else {
      responseText(resp)
    }
  })
}
