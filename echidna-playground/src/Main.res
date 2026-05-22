// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Coq-Jr Contributors

// Main entry point for Coq-Jr

// Re-export modules
module Dom = Dom
module JsCoq = JsCoq
module Components = Components
module Page = Page

// Initialize the application when running in browser
let initialize = () => {
  Console.log("Coq-Jr initialized")
  Console.log("Generated page HTML available via Page.render()")
}

// Export the page render function for use by Deno server
let getPageHtml = Page.render
