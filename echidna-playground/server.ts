// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Coq-Jr Contributors

// Deno HTTP server for Coq-Jr

const PORT = 8000;

// Import the compiled ReScript page renderer
// After running `npm run res:build`, the compiled JS will be available
let getPageHtml: () => string;

try {
  const mainModule = await import("./src/Main.res.js");
  getPageHtml = mainModule.getPageHtml;
} catch {
  // Fallback if ReScript hasn't been compiled yet
  getPageHtml = () => `
<!DOCTYPE html>
<html>
  <head>
    <meta charset="utf-8">
    <title>Coq-Jr - Build Required</title>
    <style>
      body { font-family: system-ui, sans-serif; max-width: 800px; margin: 50px auto; padding: 20px; }
      code { background: #f4f4f4; padding: 2px 6px; border-radius: 3px; }
      pre { background: #f4f4f4; padding: 15px; border-radius: 5px; overflow-x: auto; }
    </style>
  </head>
  <body>
    <h1>Coq-Jr</h1>
    <p>The ReScript sources need to be compiled first.</p>
    <h2>Quick Start</h2>
    <pre><code>npm install
npm run res:build
deno task serve</code></pre>
  </body>
</html>`;
}

const MIME_TYPES: Record<string, string> = {
  ".html": "text/html",
  ".css": "text/css",
  ".js": "application/javascript",
  ".json": "application/json",
  ".png": "image/png",
  ".jpg": "image/jpeg",
  ".jpeg": "image/jpeg",
  ".gif": "image/gif",
  ".svg": "image/svg+xml",
  ".ico": "image/x-icon",
  ".woff": "font/woff",
  ".woff2": "font/woff2",
};

function getMimeType(path: string): string {
  const ext = path.substring(path.lastIndexOf("."));
  return MIME_TYPES[ext] || "application/octet-stream";
}

async function serveStaticFile(path: string): Promise<Response | null> {
  try {
    const file = await Deno.readFile(path);
    return new Response(file, {
      headers: { "content-type": getMimeType(path) },
    });
  } catch {
    return null;
  }
}

async function handler(request: Request): Promise<Response> {
  const url = new URL(request.url);
  let pathname = url.pathname;

  console.log(`${request.method} ${pathname}`);

  // Serve index page
  if (pathname === "/" || pathname === "/index.html") {
    return new Response(getPageHtml(), {
      headers: { "content-type": "text/html; charset=utf-8" },
    });
  }

  // Try to serve static files
  const staticPath = `.${pathname}`;
  const staticResponse = await serveStaticFile(staticPath);
  if (staticResponse) {
    return staticResponse;
  }

  // 404 for everything else
  return new Response("Not Found", { status: 404 });
}

console.log(`Coq-Jr server running at http://localhost:${PORT}/`);
Deno.serve({ port: PORT }, handler);
