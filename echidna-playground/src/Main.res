// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Coq-Jr Contributors

// Main entry point for Coq-Jr

// Re-export modules
module Dom = Dom
module JsCoq = JsCoq
module Components = Components
module Page = Page

// Initialize the application when running in browser
let initialize = () => {
  Js.log("Coq-Jr initialized")
  Js.log("Generated page HTML available via Page.render()")
}

// Export the page render function for use by Deno server
let getPageHtml = Page.render
