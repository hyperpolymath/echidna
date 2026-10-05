// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)
//
// serve-static.js — minimal local static file server for the UI shell.
// Replaces the retired `deno run jsr:@std/http/file-server` recipe.
// Usage (from the directory to serve): bun path/to/serve-static.js [port]
// Local development only: binds 127.0.0.1, serves the current directory.

import { resolve, sep } from "node:path";

const root = resolve(process.cwd());
const port = Number(process.argv[2] ?? "3000");

/**
 * Map a request URL path to a file under `root`, or null when the path
 * escapes `root` or is malformed. "/" maps to index.html.
 * @param {string} pathname
 * @returns {string | null}
 */
function resolveRequestPath(pathname) {
  let decoded;
  try {
    decoded = decodeURIComponent(pathname);
  } catch {
    return null;
  }
  const rel = decoded === "/" ? "index.html" : decoded.replace(/^\/+/, "");
  const full = resolve(root, rel);
  return full === root || full.startsWith(root + sep) ? full : null;
}

Bun.serve({
  hostname: "127.0.0.1",
  port,
  /** Serve the requested file, 404 when absent, 403 when outside root. */
  async fetch(req) {
    const path = resolveRequestPath(new URL(req.url).pathname);
    if (path === null) return new Response("forbidden", { status: 403 });
    const file = Bun.file(path);
    return (await file.exists())
      ? new Response(file)
      : new Response("not found", { status: 404 });
  },
});

console.log(`serving ${root} on http://127.0.0.1:${port}`);
