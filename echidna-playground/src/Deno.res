// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Coq-Jr Contributors

// Deno HTTP server bindings for ReScript

type request
type response

// Deno namespace bindings
@val @scope("Deno") external readFile: string => Js.Promise.t<Js.TypedArray2.Uint8Array.t> = "readFile"

type serveOptions = {port: int}
type serveHandler = request => Js.Promise.t<response>

@val @scope("Deno") external serve: (serveOptions, serveHandler) => unit = "serve"

// Request bindings
@get external getUrl: request => string = "url"
@get external getMethod: request => string = "method"

// Response constructor
@new external makeResponse: (string, {"headers": {"content-type": string}}) => response = "Response"
@new external makeResponseWithStatus: (string, {"status": int}) => response = "Response"
@new external makeResponseBytes: (Js.TypedArray2.Uint8Array.t, {"headers": {"content-type": string}}) => response = "Response"

// URL parsing
type url = {pathname: string}
@new external makeUrl: string => url = "URL"

// Console
@val @scope("console") external log: string => unit = "log"
