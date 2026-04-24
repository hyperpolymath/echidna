// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)

/**
 * ECHIDNA Continuous Proof Runner Daemon
 * Runs proof attempts continuously, day and night.
 * Manages a priority queue of problems, concurrent solving,
 * health checking, retry logic, and result persistence.
 */

/** FFI: console.log */
@scope("console") @val
external log: string => unit = "log"

/** FFI: console.error */
@scope("console") @val
external consoleError: (string, 'a) => unit = "error"

/** FFI: Deno.mkdir */
@scope("Deno") @val
external mkdir: (string, {"recursive": bool}) => promise<unit> = "mkdir"

/** FFI: Deno.writeTextFile */
@scope("Deno") @val
external writeTextFile: (string, string) => promise<unit> = "writeTextFile"

/** FFI: Deno.readTextFile */
@scope("Deno") @val
external readTextFile: string => promise<string> = "readTextFile"

/** FFI: JSON.stringify with indent */
@scope("JSON") @val
external jsonStringify2: ('a, Js.null<'b>, int) => string = "stringify"

/** FFI: JSON.parse */
@scope("JSON") @val
external jsonParse: string => 'a = "parse"

/** FFI: Date.now */
@scope("Date") @val
external dateNow: unit => float = "now"

/** FFI: setTimeout as promise for delays */
let sleep = (ms: int): promise<unit> => {
  Js.Promise2.make((~resolve, ~reject as _) => {
    let _ = Js.Global.setTimeout(() => resolve(), ms)
  })
}

/** Daemon configuration */
type daemonConfig = {
  /** Interval between queue checks (ms) */
  pollInterval: int,
  /** Maximum concurrent proof attempts */
  maxConcurrent: int,
  /** Maximum retries per problem */
  maxRetries: int,
  /** Timeout per problem (seconds) */
  defaultTimeout: int,
  /** Strategy for prover selection */
  strategy: string,
  /** Enable persistent storage */
  persistResults: bool,
  /** Results storage path */
  storagePath: string,
  /** Health check interval (ms) */
  healthCheckInterval: int,
}

/** Default daemon configuration */
let defaultConfig: daemonConfig = {
  pollInterval: 1000,
  maxConcurrent: 5,
  maxRetries: 3,
  defaultTimeout: 60,
  strategy: "cascade",
  persistResults: true,
  storagePath: "./echidna_results",
  healthCheckInterval: 60000,
}

/** Daemon statistics */
type daemonStats = {
  started: float,
  mutable problemsQueued: int,
  mutable problemsCompleted: int,
  mutable problemsFailed: int,
  mutable proofsFound: int,
  mutable totalTimeMs: int,
  mutable uptimeMs: float,
  mutable currentRunning: int,
}

/** Queue item wrapping a problem with metadata */
type queueItem = {
  problem: Prover.problem,
  provers: array<string>,
  priority: int,
  created: float,
  mutable attempts: int,
}

/** Health check result entry */
type healthEntry = {
  name: string,
  available: bool,
}

/** Daemon event types for event handlers */
type daemonEvent =
  | Started
  | Stopped
  | ProblemQueued({problem: Prover.problem})
  | ProblemStarted({problem: Prover.problem})
  | ProblemCompleted({result: Unified.unifiedResult})
  | ProblemFailed({problem: Prover.problem, error: string})
  | HealthCheck({results: array<healthEntry>})

/** Event handler function type */
type eventHandler = daemonEvent => promise<unit>

/** Daemon instance state */
type t = {
  config: daemonConfig,
  client: Unified.t,
  mutable queue: array<queueItem>,
  mutable runningCount: int,
  results: Js.Dict.t<Unified.unifiedResult>,
  stats: daemonStats,
  mutable isRunning: bool,
  mutable eventHandlers: array<eventHandler>,
}

/** Create a new daemon instance with the given config */
let make = (config: daemonConfig): t => {
  config: config,
  client: Unified.makeClientWithTimeout(~timeoutSec=config.defaultTimeout),
  queue: [],
  runningCount: 0,
  results: Js.Dict.empty(),
  stats: {
    started: dateNow(),
    problemsQueued: 0,
    problemsCompleted: 0,
    problemsFailed: 0,
    proofsFound: 0,
    totalTimeMs: 0,
    uptimeMs: 0.0,
    currentRunning: 0,
  },
  isRunning: false,
  eventHandlers: [],
}

/** Register an event handler */
let on = (daemon: t, handler: eventHandler): unit => {
  daemon.eventHandlers = Array.concat(daemon.eventHandlers, [handler])
}

/** Emit an event to all registered handlers */
let emit = async (daemon: t, event: daemonEvent): unit => {
  let handlers = daemon.eventHandlers
  for i in 0 to Array.length(handlers) - 1 {
    try {
      switch handlers->Array.get(i) {
      | Some(handler) => await handler(event)
      | None => ()
      }
    } catch {
    | exn => consoleError("[Daemon] Event handler error:", exn)
    }
  }
}

/** Enqueue a problem for solving */
let enqueue = (daemon: t, ~problem: Prover.problem, ~provers: option<array<string>>=?, ~priority: int=0): unit => {
  let item: queueItem = {
    problem: problem,
    provers: Belt.Option.getWithDefault(provers, []),
    priority: priority,
    created: dateNow(),
    attempts: 0,
  }

  // Insert by priority (higher priority first)
  let idx = daemon.queue->Array.findIndex(q => q.priority < priority)
  if idx == -1 {
    daemon.queue = Array.concat(daemon.queue, [item])
  } else {
    let before = daemon.queue->Array.slice(~start=0, ~end=idx)
    let after = daemon.queue->Array.sliceToEnd(~start=idx)
    daemon.queue = Array.concatMany([before, [item], after])
  }

  daemon.stats.problemsQueued = daemon.stats.problemsQueued + 1
  let _ = emit(daemon, ProblemQueued({problem: problem}))

  log(`[Daemon] Queued: ${problem.id} (priority: ${Belt.Int.toString(priority)}, queue size: ${Belt.Int.toString(Array.length(daemon.queue))})`)
}

/** Enqueue multiple problems at once */
let enqueueBatch = (daemon: t, problems: array<Prover.problem>): unit => {
  problems->Array.forEach(problem => {
    enqueue(daemon, ~problem, ~priority=0)
  })
}

/** Process a single queue item */
let processItem = async (daemon: t, item: queueItem): unit => {
  let _ = await emit(daemon, ProblemStarted({problem: item.problem}))

  try {
    let proversOpt = if Array.length(item.provers) > 0 { Some(item.provers) } else { None }
    let result = await Unified.solveWithStrategy(
      daemon.client,
      ~problem=item.problem,
      ~strategy=daemon.config.strategy,
      ~provers=proversOpt,
    )

    // Store result
    Js.Dict.set(daemon.results, item.problem.id, result)
    item.attempts = item.attempts + 1

    // Update stats
    daemon.stats.totalTimeMs = daemon.stats.totalTimeMs + result.totalTimeMs

    switch result.bestResult {
    | Some(best) =>
      switch best.status {
      | "theorem" | "unsatisfiable" =>
        daemon.stats.proofsFound = daemon.stats.proofsFound + 1
        daemon.stats.problemsCompleted = daemon.stats.problemsCompleted + 1
        log(`[Daemon] PROVED: ${item.problem.id} by ${best.prover} (${Belt.Int.toString(best.timeMs)}ms)`)
      | "satisfiable" | "countersatisfiable" =>
        daemon.stats.problemsCompleted = daemon.stats.problemsCompleted + 1
        log(`[Daemon] Counterexample: ${item.problem.id} by ${best.prover}`)
      | "timeout" | "unknown" =>
        if item.attempts < daemon.config.maxRetries {
          log(`[Daemon] ? Retry ${Belt.Int.toString(item.attempts)}/${Belt.Int.toString(daemon.config.maxRetries)}: ${item.problem.id}`)
          daemon.queue = Array.concat(daemon.queue, [item])
        } else {
          daemon.stats.problemsFailed = daemon.stats.problemsFailed + 1
          log(`[Daemon] Failed after ${Belt.Int.toString(item.attempts)} attempts: ${item.problem.id}`)
        }
      | _ =>
        daemon.stats.problemsFailed = daemon.stats.problemsFailed + 1
      }
      let _ = await emit(daemon, ProblemCompleted({result: result}))
    | None =>
      if item.attempts < daemon.config.maxRetries {
        daemon.queue = Array.concat(daemon.queue, [item])
      } else {
        daemon.stats.problemsFailed = daemon.stats.problemsFailed + 1
        let _ = await emit(daemon, ProblemFailed({
          problem: item.problem,
          error: "No result from any prover",
        }))
      }
    }
  } catch {
  | exn =>
    let errorMsg = Js.String.make(exn)
    consoleError(`[Daemon] Error processing ${item.problem.id}:`, errorMsg)

    if item.attempts < daemon.config.maxRetries {
      item.attempts = item.attempts + 1
      daemon.queue = Array.concat(daemon.queue, [item])
    } else {
      daemon.stats.problemsFailed = daemon.stats.problemsFailed + 1
      let _ = await emit(daemon, ProblemFailed({
        problem: item.problem,
        error: errorMsg,
      }))
    }
  }

  daemon.runningCount = daemon.runningCount - 1
}

/** Save results to disk as JSON */
let saveResults = async (daemon: t): unit => {
  try {
    await mkdir(daemon.config.storagePath, {"recursive": true})

    let data = {
      "stats": daemon.stats,
      "results": daemon.results,
      "timestamp": Js.Date.make()->Js.Date.toISOString,
    }

    let filename = `${daemon.config.storagePath}/results_${Belt.Float.toString(dateNow())}.json`
    await writeTextFile(filename, jsonStringify2(data, Js.null, 2))
    log(`[Daemon] Results saved to ${filename}`)
  } catch {
  | exn => consoleError("[Daemon] Failed to save results:", exn)
  }
}

/** Main processing loop — dequeues and processes items up to concurrency limit */
let rec mainLoop = async (daemon: t): unit => {
  if daemon.isRunning {
    // Update uptime
    daemon.stats.uptimeMs = dateNow() -. daemon.stats.started

    // Process queue if we have capacity
    while Array.length(daemon.queue) > 0 && daemon.runningCount < daemon.config.maxConcurrent {
      switch daemon.queue->Array.shift {
      | Some(item) =>
        daemon.runningCount = daemon.runningCount + 1
        daemon.stats.currentRunning = daemon.runningCount
        let _ = processItem(daemon, item)
      | None => ()
      }
    }

    daemon.stats.currentRunning = daemon.runningCount

    await sleep(daemon.config.pollInterval)
    await mainLoop(daemon)
  }
}

/** Health check loop — periodically checks prover service health */
let rec healthCheckLoop = async (daemon: t): unit => {
  if daemon.isRunning {
    await sleep(daemon.config.healthCheckInterval)

    if daemon.isRunning {
      let health = await Unified.healthCheck(daemon.client)
      let entries = health->Array.map(h => ({name: h.name, available: h.available}: healthEntry))
      let _ = await emit(daemon, HealthCheck({results: entries}))
    }

    await healthCheckLoop(daemon)
  }
}

/** Start the daemon — performs initial health check then enters main loop */
let start = async (daemon: t): unit => {
  if daemon.isRunning {
    log("[Daemon] Already running")
  } else {
    daemon.isRunning = true
    daemon.stats.started = dateNow()
    daemon.stats.problemsQueued = 0
    daemon.stats.problemsCompleted = 0
    daemon.stats.problemsFailed = 0
    daemon.stats.proofsFound = 0
    daemon.stats.totalTimeMs = 0
    daemon.stats.uptimeMs = 0.0
    daemon.stats.currentRunning = 0

    log("[Daemon] Starting ECHIDNA Proof Runner...")
    log(`[Daemon] Config: ${jsonStringify2(daemon.config, Js.null, 2)}`)

    // Initial health check
    let health = await Unified.healthCheck(daemon.client)
    log("[Daemon] Service health:")
    health->Array.forEach(h => {
      let mark = if h.available { "✓" } else { "✗" }
      log(`  - ${h.name}: ${mark} (${Belt.Int.toString(h.provers)} provers)`)
    })

    let _ = await emit(daemon, Started)

    // Start loops (fire-and-forget)
    let _ = mainLoop(daemon)
    let _ = healthCheckLoop(daemon)

    log("[Daemon] Running continuously. Press Ctrl+C to stop.")
  }
}

/** Stop the daemon — waits for running tasks, persists results */
let stop = async (daemon: t): unit => {
  if daemon.isRunning {
    log("[Daemon] Stopping...")
    daemon.isRunning = false

    // Wait briefly for running tasks
    if daemon.runningCount > 0 {
      log(`[Daemon] Waiting for ${Belt.Int.toString(daemon.runningCount)} tasks to complete...`)
      await sleep(2000)
    }

    // Persist results
    if daemon.config.persistResults {
      await saveResults(daemon)
    }

    let _ = await emit(daemon, Stopped)
    log("[Daemon] Stopped")
  }
}

/** Load problems from a JSON file and enqueue them */
let loadProblemsFromFile = async (daemon: t, path: string): unit => {
  let content = await readTextFile(path)
  let problems: array<Prover.problem> = jsonParse(content)
  enqueueBatch(daemon, problems)
}

/** Get current daemon statistics */
let getStats = (daemon: t): daemonStats => {
  {
    ...daemon.stats,
    uptimeMs: dateNow() -. daemon.stats.started,
    currentRunning: daemon.runningCount,
  }
}

/** Get current queue status */
let getQueueStatus = (daemon: t): {
  "pending": int,
  "running": int,
  "completed": int,
} => {
  {
    "pending": Array.length(daemon.queue),
    "running": daemon.runningCount,
    "completed": Js.Dict.keys(daemon.results)->Array.length,
  }
}

/** Get result for a specific problem by ID */
let getResult = (daemon: t, problemId: string): option<Unified.unifiedResult> => {
  Js.Dict.get(daemon.results, problemId)
}
