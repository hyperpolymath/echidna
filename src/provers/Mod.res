// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)

/**
 * ECHIDNA Prover Integration Module
 * Barrel re-export of all prover types, clients, runners, and utilities.
 * Deno-native theorem prover integration (NO NPM).
 *
 * Types: Prover, ProverResult, Problem, QueueItem, ProverConfig, etc.
 * Clients: SystemOnTPTP, Metamath, Z3Wasm, Wolfram, LeanTool, Unified
 * Runners: ProofRunnerDaemon
 * Utilities: HTTP helpers with retry logic
 */

// NOTE: ReScript does not have barrel re-exports like TypeScript.
// Each module (Prover.res, LeanTool.res, Metamath.res, etc.) is
// automatically available by name. This file documents the public API
// surface for the prover subsystem.
//
// Module Map:
//   Types:    Prover (types, DEFAULT_CONFIG, PROVER_REGISTRY)
//   Clients:  SystemOnTptp, Metamath, Z3Wasm, Wolfram, LeanTool, Unified
//   Runners:  Daemon (ProofRunnerDaemon, DaemonConfig, DaemonStats, DaemonEvent)
//   Utils:    Http (fetchWithRetry, postForm, postJSON, getText, sleep, backoffDelay)

/** Re-export key type aliases for convenience */
type inputFormat = Prover.inputFormat
type proverStatus = Prover.proverStatus
type prover = Prover.prover
type proverResult = Prover.proverResult
type problem = Prover.problem
type queueItem = Prover.queueItem
type proverConfig = Prover.proverConfig
