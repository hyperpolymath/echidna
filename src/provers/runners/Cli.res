// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)

/**
 * ECHIDNA Proof Runner CLI
 * Command-line interface for running the proof daemon.
 *
 * Usage:
 *   deno run --allow-net --allow-read --allow-write --allow-env Cli.res.js [options]
 *
 * Options:
 *   --help              Show help
 *   --health            Check service health
 *   --solve <file>      Solve a single problem file
 *   --batch <dir>       Process all problems in directory
 *   --daemon            Run as continuous daemon
 *   --format <fmt>      Input format (tptp, smtlib2, metamath, lean)
 *   --prover <id>       Specific prover to use
 *   --timeout <sec>     Timeout in seconds (default: 60)
 *   --strategy <s>      Strategy: first, cascade, parallel, all (default: cascade)
 *   --output <file>     Output results to file
 */

/** FFI: Deno.args */
@scope("Deno") @val
external denoArgs: array<string> = "args"

/** FFI: Deno.readTextFile */
@scope("Deno") @val
external readTextFile: string => promise<string> = "readTextFile"

/** FFI: Deno.writeTextFile */
@scope("Deno") @val
external writeTextFile: (string, string) => promise<unit> = "writeTextFile"

/** FFI: Deno.readDir */
@scope("Deno") @val
external readDir: string => Js.AsyncIterator.t<{"name": string, "isFile": bool}> = "readDir"

/** FFI: Deno.exit */
@scope("Deno") @val
external exit: int => unit = "exit"

/** FFI: Deno.addSignalListener */
@scope("Deno") @val
external addSignalListener: (string, unit => unit) => unit = "addSignalListener"

/** FFI: console.log */
@scope("console") @val
external log: string => unit = "log"

/** FFI: console.error */
@scope("console") @val
external error: string => unit = "error"

/** FFI: JSON.stringify with indent */
@scope("JSON") @val
external jsonStringify2: ('a, Js.null<'b>, int) => string = "stringify"

/** FFI: JSON.parse */
@scope("JSON") @val
external jsonParse: string => 'a = "parse"

/** FFI: setTimeout as promise */
let delay = (ms: int): promise<unit> => {
  Js.Promise2.make((~resolve, ~reject as _) => {
    let _ = Js.Global.setTimeout(() => resolve(), ms)
  })
}

/** Selection strategy for provers */
type strategy =
  | @as("first") First
  | @as("cascade") Cascade
  | @as("parallel") Parallel
  | @as("all") All

/** CLI arguments parsed from command line */
type cliArgs = {
  mutable help: bool,
  mutable health: bool,
  mutable solve: option<string>,
  mutable batch: option<string>,
  mutable daemon: bool,
  mutable format: string,
  mutable prover: option<string>,
  mutable timeout: int,
  mutable strategy: string,
  mutable output: option<string>,
}

/** Create default CLI arguments */
let makeDefaultArgs = (): cliArgs => {
  help: false,
  health: false,
  solve: None,
  batch: None,
  daemon: false,
  format: "tptp",
  prover: None,
  timeout: 60,
  strategy: "cascade",
  output: None,
}

/** Parse command line arguments from Deno.args */
let parseArgs = (): cliArgs => {
  let args = makeDefaultArgs()
  let argv = denoArgs
  let len = Array.length(argv)
  let i = ref(0)

  while i.contents < len {
    let arg = argv->Array.getUnsafe(i.contents)
    switch arg {
    | "--help" | "-h" => args.help = true
    | "--health" => args.health = true
    | "--solve" =>
      i := i.contents + 1
      if i.contents < len {
        args.solve = Some(argv->Array.getUnsafe(i.contents))
      }
    | "--batch" =>
      i := i.contents + 1
      if i.contents < len {
        args.batch = Some(argv->Array.getUnsafe(i.contents))
      }
    | "--daemon" => args.daemon = true
    | "--format" =>
      i := i.contents + 1
      if i.contents < len {
        args.format = argv->Array.getUnsafe(i.contents)
      }
    | "--prover" =>
      i := i.contents + 1
      if i.contents < len {
        args.prover = Some(argv->Array.getUnsafe(i.contents))
      }
    | "--timeout" =>
      i := i.contents + 1
      if i.contents < len {
        switch Belt.Int.fromString(argv->Array.getUnsafe(i.contents)) {
        | Some(t) => args.timeout = t
        | None => ()
        }
      }
    | "--strategy" =>
      i := i.contents + 1
      if i.contents < len {
        args.strategy = argv->Array.getUnsafe(i.contents)
      }
    | "--output" =>
      i := i.contents + 1
      if i.contents < len {
        args.output = Some(argv->Array.getUnsafe(i.contents))
      }
    | _ => ()
    }
    i := i.contents + 1
  }

  args
}

/** Print help message to console */
let printHelp = (): unit => {
  log(`
ECHIDNA Proof Runner - Neurosymbolic Theorem Proving Platform

Usage:
  echidna-runner [options]

Options:
  -h, --help              Show this help message
  --health                Check health of all prover services
  --solve <file>          Solve a single problem from file
  --batch <dir>           Process all problems in directory
  --daemon                Run as continuous daemon (day and night)
  --format <fmt>          Input format: tptp, smtlib2, metamath, lean, wolfram
  --prover <id>           Use specific prover (e.g., Vampire---4.8, z3-wasm)
  --timeout <sec>         Timeout in seconds (default: 60)
  --strategy <s>          Selection strategy:
                            first    - Use first available prover
                            cascade  - Try in order until success (default)
                            parallel - Run all in parallel
                            all      - Run all, return best result
  --output <file>         Write results to JSON file

Examples:
  # Check service availability
  echidna-runner --health

  # Solve a TPTP problem
  echidna-runner --solve problem.p --format tptp

  # Solve with specific prover
  echidna-runner --solve problem.smt2 --format smtlib2 --prover z3-wasm

  # Run all provers in parallel
  echidna-runner --solve problem.p --strategy parallel

  # Process directory of problems
  echidna-runner --batch ./problems --format tptp --output results.json

  # Run as continuous daemon
  echidna-runner --daemon

Environment Variables:
  WOLFRAM_APP_ID      Wolfram Alpha API key
  LEANTOOL_API_KEY    LeanTool API key
  LEANTOOL_ENDPOINT   Custom LeanTool endpoint

Available Provers:
  SystemOnTPTP: Vampire, E, Z3, CVC5, SPASS, Prover9, Leo-III, Satallax, etc.
  Local:        z3-wasm, metamath-verify
  APIs:         wolfram-prove, wolfram-solve, lean4, lean4-mathlib
`)
}

/** Separator line for console output */
let separator = String.make(~count=50, `\u2500`)
let doubleSeparator = String.make(~count=50, `\u2550`)

/** Check health of all prover services */
let checkHealth = async (): unit => {
  log("Checking ECHIDNA prover service health...\n")

  let client = Unified.makeClient()
  let health = await Unified.healthCheck(client)

  log("Service Status:")
  log(separator)

  health->Array.forEach(h => {
    let status = if h.available { "✓ Online" } else { "✗ Offline" }
    let latency = switch h.latencyMs {
    | Some(ms) => Belt.Int.toString(ms) ++ "ms"
    | None => "N/A"
    }
    log(`  ${Js.String2.padEnd(h.name, 20, " ")} ${Js.String2.padEnd(status, 12, " ")} ${latency} (${Belt.Int.toString(h.provers)} provers)`)
  })

  log(separator)

  let stats = Unified.getStats(client)
  log(`\nTotal: ${Belt.Int.toString(stats.totalProvers)} provers across ${Belt.Int.toString(stats.backends)} backends`)
  log(`Healthy: ${Belt.Int.toString(stats.healthyBackends)}/${Belt.Int.toString(stats.backends)} backends`)
}

/** Solve a single problem from a file path */
let solveSingle = async (
  ~path: string,
  ~format: string,
  ~prover: option<string>,
  ~timeout: option<int>,
  ~strategy: string,
): array<Prover.proverResult> => {
  let content = await readTextFile(path)

  let parts = Js.String2.split(path, "/")
  let name = parts->Array.getUnsafe(Array.length(parts) - 1)

  let problem: Prover.problem = {
    id: path,
    name: Some(name),
    format: format,
    content: content,
    timeoutSec: timeout,
  }

  log(`\nSolving: ${path}`)
  log(`Format: ${format}`)
  switch prover {
  | Some(p) => log(`Prover: ${p}`)
  | None => ()
  }
  log(`Strategy: ${strategy}`)
  log(separator)

  let client = Unified.makeClientWithTimeout(~timeoutSec=Belt.Option.getWithDefault(timeout, 60))
  let proversArr = switch prover {
  | Some(p) => Some([p])
  | None => None
  }
  let result = await Unified.solveWithStrategy(client, ~problem, ~strategy, ~provers=proversArr)

  // Print results
  result.results->Array.forEach(r => {
    let emoji = switch r.status {
    | "theorem" | "unsatisfiable" => "✓"
    | "satisfiable" | "countersatisfiable" => "✗"
    | "timeout" => "⏱"
    | _ => "?"
    }

    log(`\n${emoji} ${r.prover}: ${r.status} (${Belt.Int.toString(r.timeMs)}ms)`)

    switch r.proof {
    | Some(proof) =>
      log("  Proof:")
      let lines = Js.String2.split(proof, "\n")
      let preview = lines->Array.slice(~start=0, ~end=5)->Array.join("\n  ")
      log("  " ++ preview)
    | None => ()
    }

    switch r.model {
    | Some(model) =>
      log("  Model:")
      let lines = Js.String2.split(model, "\n")
      let preview = lines->Array.slice(~start=0, ~end=5)->Array.join("\n  ")
      log("  " ++ preview)
    | None => ()
    }

    switch r.error {
    | Some(err) => log(`  Error: ${err}`)
    | None => ()
    }
  })

  log(separator)
  log(`Total time: ${Belt.Int.toString(result.totalTimeMs)}ms`)

  switch result.bestResult {
  | Some(best) => log(`\nBest result: ${best.prover} - ${best.status}`)
  | None => ()
  }

  result.results
}

/** Process a batch of problems from a directory */
let processBatch = async (
  ~dir: string,
  ~format: string,
  ~prover: option<string>,
  ~timeout: option<int>,
  ~strategy: string,
  ~output: option<string>,
): unit => {
  let daemon = Daemon.make({
    defaultTimeout: Belt.Option.getWithDefault(timeout, 60),
    strategy: strategy,
    persistResults: Belt.Option.isSome(output),
    storagePath: switch output {
    | Some(o) => Js.String2.replaceByRe(o, %re("/\\.json$/"), "")
    | None => "./echidna_results"
    },
    pollInterval: 1000,
    maxConcurrent: 5,
    maxRetries: 3,
    healthCheckInterval: 60000,
  })

  // File extension mapping by format
  let exts = switch format {
  | "tptp" => [".p", ".tptp", ".ax"]
  | "smtlib2" => [".smt2", ".smt"]
  | "metamath" => [".mm"]
  | "lean" => [".lean"]
  | "dimacs" => [".cnf", ".dimacs"]
  | _ => [".p"]
  }

  log(`\nScanning ${dir} for ${format} problems...`)

  // Read directory entries and enqueue matching files
  let entries = readDir(dir)
  let rec loop = async () => {
    let next = await Js.AsyncIterator.next(entries)
    if !next.done {
      switch next.value {
      | Some(entry) =>
        if entry["isFile"] && exts->Array.some(ext => Js.String2.endsWith(entry["name"], ext)) {
          let path = `${dir}/${entry["name"]}`
          let content = await readTextFile(path)
          let problem: Prover.problem = {
            id: path,
            name: Some(entry["name"]),
            format: format,
            content: content,
            timeoutSec: timeout,
          }
          let proversArr = switch prover {
          | Some(p) => Some([p])
          | None => None
          }
          Daemon.enqueue(daemon, ~problem, ~provers=proversArr, ~priority=0)
        }
        await loop()
      | None => ()
      }
    }
  }
  await loop()

  let status = Daemon.getQueueStatus(daemon)
  log(`Queued ${Belt.Int.toString(status.pending)} problems\n`)

  if status.pending == 0 {
    log("No problems found!")
  } else {
    // Run until queue is empty
    await Daemon.start(daemon)

    // Wait for completion
    let rec waitLoop = async () => {
      let s = Daemon.getQueueStatus(daemon)
      if s.pending > 0 || s.running > 0 {
        await delay(1000)
        await waitLoop()
      }
    }
    await waitLoop()

    await Daemon.stop(daemon)

    // Print summary
    let stats = Daemon.getStats(daemon)
    log("\n" ++ doubleSeparator)
    log("BATCH PROCESSING COMPLETE")
    log(doubleSeparator)
    log(`Problems processed: ${Belt.Int.toString(stats.problemsCompleted + stats.problemsFailed)}`)
    log(`Proofs found: ${Belt.Int.toString(stats.proofsFound)}`)
    log(`Failed: ${Belt.Int.toString(stats.problemsFailed)}`)
    log(`Total time: ${Belt.Int.toString(stats.totalTimeMs)}ms`)
  }
}

/** Run as a continuous daemon process */
let runDaemon = async (): unit => {
  let daemon = Daemon.make({
    pollInterval: 1000,
    maxConcurrent: 5,
    maxRetries: 3,
    defaultTimeout: 60,
    strategy: "cascade",
    persistResults: true,
    storagePath: "./echidna_results",
    healthCheckInterval: 60000,
  })

  // Add event logging
  Daemon.on(daemon, async event => {
    switch event {
    | Daemon.Started => log("\nECHIDNA Daemon started")
    | Daemon.Stopped => log("\nECHIDNA Daemon stopped")
    | Daemon.HealthCheck({results}) =>
      let online = results->Array.filter(r => r.available)->Array.length
      log(`\nHealth: ${Belt.Int.toString(online)}/${Belt.Int.toString(Array.length(results))} services online`)
    | _ => ()
    }
  })

  // Handle shutdown signals
  let shutdown = () => {
    log("\nReceived shutdown signal...")
    let _ = Daemon.stop(daemon)
    exit(0)
  }

  addSignalListener("SIGINT", shutdown)
  addSignalListener("SIGTERM", shutdown)

  log(`
+========================================================+
|  ECHIDNA - Neurosymbolic Theorem Proving Daemon         |
|  Running continuously... Press Ctrl+C to stop           |
+========================================================+
`)

  // Check for initial problems from queue file
  try {
    let queueFile = "./echidna_queue.json"
    let content = await readTextFile(queueFile)
    let problems: array<Prover.problem> = jsonParse(content)
    Daemon.enqueueBatch(daemon, problems)
    log(`Loaded ${Belt.Int.toString(Array.length(problems))} problems from queue file`)
  } catch {
  | _ =>
    log("No queue file found. Add problems via API or queue file.")
    log("Create echidna_queue.json with array of Problem objects.")
  }

  await Daemon.start(daemon)

  // Keep running until stopped, printing periodic status
  let rec statusLoop = async () => {
    await delay(10000)

    let stats = Daemon.getStats(daemon)
    let queue = Daemon.getQueueStatus(daemon)

    let now = Js.Date.make()->Js.Date.toISOString

    log(
      `[${now}] ` ++
      `Queue: ${Belt.Int.toString(queue.pending)} | Running: ${Belt.Int.toString(queue.running)} | ` ++
      `Completed: ${Belt.Int.toString(stats.problemsCompleted)} | Proofs: ${Belt.Int.toString(stats.proofsFound)}`
    )

    await statusLoop()
  }
  await statusLoop()
}

/** Main entry point — parses args and dispatches to appropriate handler */
let main = async (): unit => {
  let args = parseArgs()

  if args.help {
    printHelp()
  } else if args.health {
    await checkHealth()
  } else {
    switch args.solve {
    | Some(path) =>
      let results = await solveSingle(
        ~path,
        ~format=args.format,
        ~prover=args.prover,
        ~timeout=Some(args.timeout),
        ~strategy=args.strategy,
      )
      switch args.output {
      | Some(outputPath) =>
        await writeTextFile(outputPath, jsonStringify2(results, Js.null, 2))
        log(`\nResults written to ${outputPath}`)
      | None => ()
      }
    | None =>
      switch args.batch {
      | Some(dir) =>
        await processBatch(
          ~dir,
          ~format=args.format,
          ~prover=args.prover,
          ~timeout=Some(args.timeout),
          ~strategy=args.strategy,
          ~output=args.output,
        )
      | None =>
        if args.daemon {
          await runDaemon()
        } else {
          printHelp()
        }
      }
    }
  }
}

// Run if this is the main module
let _ = main()->Js.Promise2.catch(err => {
  error(`Fatal error: ${Js.String.make(err)}`)
  exit(1)
  Js.Promise2.resolve()
})
