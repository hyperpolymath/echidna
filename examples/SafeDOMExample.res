// SPDX-License-Identifier: AGPL-3.0-or-later
// Example: Using SafeDOM for formally verified DOM mounting

open SafeDOM

// Example 1: Basic mounting with error handling
let mountApp = () => {
  mountSafe(
    "#app",
    "<div><h1>Hello, World!</h1><p>Mounted safely with proofs.</p></div>",
    ~onSuccess=el => {
      Console.log("✓ App mounted successfully!")
      Console.log("Element:", el)
    },
    ~onError=err => {
      Console.error("✗ Mount failed:", err)
    }
  )
}

// Example 2: Wait for DOM ready before mounting
let mountWhenDOMReady = () => {
  mountWhenReady(
    "#app",
    "<div class='container'><h1>App Title</h1></div>",
    ~onSuccess=_ => Console.log("✓ Mounted after DOM ready"),
    ~onError=err => Console.error("✗ Failed:", err)
  )
}

// Example 3: Batch mounting (atomic - all or nothing)
let mountMultiple = () => {
  let specs = [
    {selector: "#header", html: "<header><h1>Site Title</h1></header>"},
    {selector: "#nav", html: "<nav><a href='/'>Home</a></nav>"},
    {selector: "#main", html: "<main><p>Content here</p></main>"},
    {selector: "#footer", html: "<footer>© 2026</footer>"}
  ]

  switch mountBatch(specs) {
  | Ok(elements) => {
      Console.log(`✓ Successfully mounted ${Array.length(elements)} elements`)
      elements->Array.forEach(el => Console.log("  -", el))
    }
  | Error(err) => {
      Console.error("✗ Batch mount failed:", err)
      Console.error("  (None were mounted - atomic operation)")
    }
  }
}

// Example 4: Explicit validation before mounting
let mountWithValidation = () => {
  // Validate selector first
  switch ProvenSelector.validate("#my-app") {
  | Error(e) => Console.error(`Invalid selector: ${e}`)
  | Ok(validSelector) => {
      // Validate HTML
      switch ProvenHTML.validate("<div>Content</div>") {
      | Error(e) => Console.error(`Invalid HTML: ${e}`)
      | Ok(validHtml) => {
          // Now mount with proven safety
          switch mount(validSelector, validHtml) {
          | Mounted(el) => Console.log("✓ Mounted with validated inputs:", el)
          | MountPointNotFound(s) => Console.error(`✗ Element not found: ${s}`)
          | InvalidSelector(_) => Console.error("Impossible - already validated")
          | InvalidHTML(_) => Console.error("Impossible - already validated")
          }
        }
      }
    }
}

// Example 5: Integration with TEA
module MyApp = {
  type model = {message: string}
  type msg = NoOp

  let init = () => {message: "Hello from TEA"}
  let update = (model, _msg) => model
  let view = model => `<div><h1>${model.message}</h1></div>`
}

let mountTEAApp = () => {
  let model = MyApp.init()
  let html = MyApp.view(model)

  mountWhenReady(
    "#tea-app",
    html,
    ~onSuccess=el => {
      Console.log("✓ TEA app mounted")
      // Set up event handlers, subscriptions here
    },
    ~onError=err => Console.error(`✗ TEA mount failed: ${err}`)
  )
}

// Entry point
let main = () => {
  Console.log("SafeDOM Examples")
  Console.log("================\n")

  // Choose which example to run
  mountWhenDOMReady()  // Run on DOM ready
}

// Auto-execute when module loads
main()
