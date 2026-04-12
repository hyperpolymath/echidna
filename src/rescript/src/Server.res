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
external serve: (serveOptions, Webapi.Fetch.request => promise<Webapi.Fetch.response>) => unit = "serve"

/** FFI: console.log */
@scope("console") @val
external log: string => unit = "log"

/** FFI: console.error */
@scope("console") @val
external consoleError: (string, 'a) => unit = "error"

/** FFI: fetch */
@val
external fetch: (string, {"method": string, "headers": Webapi.Fetch.headers, "body": option<Webapi.Fetch.readableStream>}) => promise<Webapi.Fetch.response> = "fetch"

/** FFI: URL constructor */
type url = {
  pathname: string,
  search: string,
}
@new external makeUrl: (string, string) => url = "URL"
@new external makeUrlFromString: string => url = "URL"

/** FFI: Request fields */
@get external getUrl: Webapi.Fetch.request => string = "url"
@get external getMethod: Webapi.Fetch.request => string = "method"
@get external getHeaders: Webapi.Fetch.request => Webapi.Fetch.headers = "headers"
@get external getBody: Webapi.Fetch.request => option<Webapi.Fetch.readableStream> = "body"

/** FFI: Response constructors */
@new external makeResponse: (string, {"status": int, "headers": Dict.t<string>}) => Webapi.Fetch.response = "Response"

/** FFI: serveDir from std */
type serveDirOptions = {
  fsRoot: string,
  urlRoot: string,
  showDirListing: bool,
  showIndex: bool,
  enableCors: bool,
}
@module("https://deno.land/std@0.211.0/http/file_server.ts")
external serveDir: (Webapi.Fetch.request, serveDirOptions) => promise<Webapi.Fetch.response> = "serveDir"

/** Server port */
let port = switch envGet("PORT") {
| Some(p) => p->Int.fromString->Option.getOr(3000)
| None => 3000
}

/** API backend URL (configurable via ECHIDNA_API_URL env var) */
let apiBackend = switch envGet("ECHIDNA_API_URL") {
| Some(url) => url
| None => "http://localhost:8081"
}

/** Request handler — proxies /api/ to Rust backend, serves static files otherwise */
let handler = async (req: Webapi.Fetch.request): Webapi.Fetch.response => {
  let reqUrl = req->getUrl
  let url = makeUrlFromString(reqUrl)

  // API proxy to Rust backend
  if url.pathname->String.startsWith("/api/") {
    try {
      let apiUrl = makeUrl(url.pathname, apiBackend)
      let targetUrl = apiUrl.pathname ++ url.search

      let response = await fetch(targetUrl, {
        "method": req->getMethod,
        "headers": req->getHeaders,
        "body": req->getBody,
      })

      response
    } catch {
    | exn =>
      consoleError("API proxy error:", exn)
      let headers = Dict.fromArray([("Content-Type", "application/json")])
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
  log(`ECHIDNA UI Server starting on port ${port->Int.toString}`)
  log(`API Backend: ${apiBackend}`)
  serve({port: port}, handler)
}

// Auto-start
let _ = start()
