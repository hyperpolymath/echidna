// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)

/**
 * Deno HTTP server for ECHIDNA Playground (echidna-playground).
 * Serves the compiled ReScript page, falling back to a build-required message.
 * Distinct from Server.res which is the Coq-Jr server in this same directory.
 */

/** FFI: Deno.readFile */
@scope("Deno") @val
external readFile: string => promise<Js.TypedArray2.Uint8Array.t> = "readFile"

/** FFI: Deno.serve */
type serveOptions = {port: int}
@scope("Deno") @val
external denoServe: (serveOptions, Deno.request => promise<Deno.response>) => unit = "serve"

/** FFI: console.log */
@scope("console") @val
external log: string => unit = "log"

/** MIME type mapping for static file serving */
let mimeTypes: Js.Dict.t<string> = Js.Dict.fromArray([
  (".html", "text/html"),
  (".css", "text/css"),
  (".js", "application/javascript"),
  (".json", "application/json"),
  (".png", "image/png"),
  (".jpg", "image/jpeg"),
  (".jpeg", "image/jpeg"),
  (".gif", "image/gif"),
  (".svg", "image/svg+xml"),
  (".ico", "image/x-icon"),
  (".woff", "font/woff"),
  (".woff2", "font/woff2"),
])

/** Extract file extension from a path */
let getExtension = (path: string): string => {
  let lastDot = Js.String2.lastIndexOf(path, ".")
  if lastDot >= 0 {
    Js.String2.substr(path, ~from=lastDot)
  } else {
    ""
  }
}

/** Look up MIME type for a path */
let getMimeType = (path: string): string => {
  let ext = getExtension(path)
  switch Js.Dict.get(mimeTypes, ext) {
  | Some(mime) => mime
  | None => "application/octet-stream"
  }
}

/** Attempt to serve a static file, returning None if not found */
let serveStaticFile = async (path: string): option<Deno.response> => {
  try {
    let bytes = await readFile(path)
    Some(Deno.makeResponseBytes(bytes, {"headers": {"content-type": getMimeType(path)}}))
  } catch {
  | _ => None
  }
}

/** Fallback HTML when ReScript hasn't been compiled yet */
let buildRequiredHtml = `
<!DOCTYPE html>
<html>
  <head>
    <meta charset="utf-8">
    <title>ECHIDNA Playground - Build Required</title>
    <style>
      body { font-family: system-ui, sans-serif; max-width: 800px; margin: 50px auto; padding: 20px; }
      code { background: #f4f4f4; padding: 2px 6px; border-radius: 3px; }
      pre { background: #f4f4f4; padding: 15px; border-radius: 5px; overflow-x: auto; }
    </style>
  </head>
  <body>
    <h1>ECHIDNA Playground</h1>
    <p>The ReScript sources need to be compiled first.</p>
    <h2>Quick Start</h2>
    <pre><code>deno task build
deno task serve</code></pre>
  </body>
</html>`

/** Try to load the compiled ReScript page renderer, falling back to static HTML */
let getPageHtml = (): string => {
  // In production, Main.res.js should provide the page content via Page.render()
  // If not available, return the build-required fallback
  try {
    Page.render()
  } catch {
  | _ => buildRequiredHtml
  }
}

/** Server port */
let port = 8000

/** Request handler */
let handler = async (request: Deno.request): Deno.response => {
  let urlStr = Deno.getUrl(request)
  let url = Deno.makeUrl(urlStr)
  let pathname = url.pathname

  log(`${Deno.getMethod(request)} ${pathname}`)

  // Serve index page
  if pathname == "/" || pathname == "/index.html" {
    Deno.makeResponse(getPageHtml(), {"headers": {"content-type": "text/html; charset=utf-8"}})
  } else {
    // Try to serve static files
    let staticPath = "." ++ pathname
    let staticResponse = await serveStaticFile(staticPath)
    switch staticResponse {
    | Some(response) => response
    | None => Deno.makeResponseWithStatus("Not Found", {"status": 404})
    }
  }
}

/** Start the playground server */
let start = () => {
  log(`ECHIDNA Playground server running at http://localhost:${Belt.Int.toString(port)}/`)
  denoServe({port: port}, handler)
}

// Auto-start when loaded
let _ = start()
