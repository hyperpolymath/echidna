// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)

/**
 * Deno development server for ECHIDNA UI.
 * Serves static files and proxies API requests to Rust backend.
 */

/** FFI: Deno.env.get */
@scope(("Deno", "env")) @val
external envGet: string => option<string> = "get"

/** FFI: Deno.serve */
type serveOptions = {port: int}
@scope("Deno") @val
external serve: (serveOptions, Fetch.request => promise<Fetch.response>) => unit = "serve"

/** FFI: console.log */
@scope("console") @val
external log: string => unit = "log"

/** FFI: console.error */
@scope("console") @val
external consoleError: (string, 'a) => unit = "error"

/** FFI: fetch */
@val
external fetch: (string, {"method": string, "headers": Fetch.headers, "body": option<Fetch.readableStream>}) => promise<Fetch.response> = "fetch"

/** FFI: URL constructor */
type url = {
  pathname: string,
  search: string,
}
@new external makeUrl: (string, string) => url = "URL"
@new external makeUrlFromString: string => url = "URL"

/** FFI: Request fields */
@get external getUrl: Fetch.request => string = "url"
@get external getMethod: Fetch.request => string = "method"
@get external getHeaders: Fetch.request => Fetch.headers = "headers"
@get external getBody: Fetch.request => option<Fetch.readableStream> = "body"

/** FFI: Response constructors */
@new external makeResponse: (string, {"status": int, "headers": Js.Dict.t<string>}) => Fetch.response = "Response"

/** FFI: serveDir from std */
type serveDirOptions = {
  fsRoot: string,
  urlRoot: string,
  showDirListing: bool,
  showIndex: bool,
  enableCors: bool,
}
@module("https://deno.land/std@0.211.0/http/file_server.ts")
external serveDir: (Fetch.request, serveDirOptions) => promise<Fetch.response> = "serveDir"

/** Server port */
let port = 8081

/** API backend URL (configurable via ECHIDNA_API_URL env var) */
let apiBackend = switch envGet("ECHIDNA_API_URL") {
| Some(url) => url
| None => "http://localhost:3000"
}

/** Request handler — proxies /api/ to Rust backend, serves static files otherwise */
let handler = async (req: Fetch.request): Fetch.response => {
  let reqUrl = getUrl(req)
  let url = makeUrlFromString(reqUrl)

  // API proxy to Rust backend
  if Js.String2.startsWith(url.pathname, "/api/") {
    try {
      let apiUrl = makeUrl(url.pathname, apiBackend)
      let targetUrl = apiUrl.pathname ++ url.search

      let response = await fetch(targetUrl, {
        "method": getMethod(req),
        "headers": getHeaders(req),
        "body": getBody(req),
      })

      response
    } catch {
    | exn =>
      consoleError("API proxy error:", exn)
      let headers = Js.Dict.fromArray([("Content-Type", "application/json")])
      makeResponse(`{"error": "Backend unavailable"}`, {"status": 502, "headers": headers})
    }
  } else {
    // Serve static files
    await serveDir(req, {
      fsRoot: ".",
      urlRoot: "",
      showDirListing: false,
      showIndex: true,
      enableCors: true,
    })
  }
}

/** Start the server */
let start = () => {
  log(`ECHIDNA UI Server starting on port ${Belt.Int.toString(port)}`)
  log(`API Backend: ${apiBackend}`)
  serve({port: port}, handler)
}

// Auto-start
let _ = start()
