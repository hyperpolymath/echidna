// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Coq-Jr Contributors

// HTTP Server for Coq-Jr in ReScript

let port = 8000

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

let getExtension = (path: string): string => {
  let lastDot = Js.String2.lastIndexOf(path, ".")
  if lastDot >= 0 {
    Js.String2.substr(path, ~from=lastDot)
  } else {
    ""
  }
}

let getMimeType = (path: string): string => {
  let ext = getExtension(path)
  switch Js.Dict.get(mimeTypes, ext) {
  | Some(mime) => mime
  | None => "application/octet-stream"
  }
}

let serveStaticFile = async (path: string): option<Deno.response> => {
  try {
    let bytes = await Deno.readFile(path)
    Some(Deno.makeResponseBytes(bytes, {"headers": {"content-type": getMimeType(path)}}))
  } catch {
  | _ => None
  }
}

let handler = async (request: Deno.request): Deno.response => {
  let urlStr = Deno.getUrl(request)
  let url = Deno.makeUrl(urlStr)
  let pathname = url.pathname

  Deno.log(`${Deno.getMethod(request)} ${pathname}`)

  // Serve index page
  if pathname == "/" || pathname == "/index.html" {
    Deno.makeResponse(Page.render(), {"headers": {"content-type": "text/html; charset=utf-8"}})
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

let start = () => {
  Deno.log(`Coq-Jr server running at http://localhost:${Belt.Int.toString(port)}/`)
  Deno.serve({port: port}, handler)
}

// Auto-start when loaded
let _ = start()
