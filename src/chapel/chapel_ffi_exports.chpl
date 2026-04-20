// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Chapel FFI Exports for ECHIDNA — C-compatible interface for Zig FFI layer.
// All 30 prover backends are supported.

use CTypes;
use parallel_proof_search;

// ---------------------------------------------------------------------------
// C-compatible proof result (fixed-size for C interop)
// ---------------------------------------------------------------------------

extern record CProofResult {
    var success: c_int;                    // 0 = false, 1 = true
    var prover_id: c_int;                  // ProverInfo.id (-1 if unknown)
    var prover_name: c_ptrConst(c_char);   // Prover name (Chapel-allocated)
    var time_seconds: c_double;            // Proof time in seconds
    var exit_code: c_int;                  // Subprocess exit code
    var tactic_count: c_int;               // Reserved for future tactic counting
    var error_message: c_ptrConst(c_char); // Error if failed (NULL if success)
    var category: c_int;                   // ProverCategory enum value
}

// ---------------------------------------------------------------------------
// Prover ID constants (match ProverInfo.id and Zig ProverKind enum)
// ---------------------------------------------------------------------------

extern "C" {
    // Interactive proof assistants
    const PROVER_AGDA: c_int      = 0;
    const PROVER_COQ: c_int       = 1;
    const PROVER_LEAN: c_int      = 2;
    const PROVER_ISABELLE: c_int  = 3;
    const PROVER_IDRIS2: c_int    = 4;
    const PROVER_FSTAR: c_int     = 5;
    const PROVER_HOL4: c_int      = 6;
    const PROVER_HOLLIGHT: c_int  = 7;
    const PROVER_NUPRL: c_int     = 8;
    const PROVER_MINLOG: c_int    = 9;

    // SMT solvers
    const PROVER_Z3: c_int        = 10;
    const PROVER_CVC5: c_int      = 11;
    const PROVER_ALTERGO: c_int   = 12;

    // First-order ATPs
    const PROVER_VAMPIRE: c_int   = 13;
    const PROVER_EPROVER: c_int   = 14;
    const PROVER_SPASS: c_int     = 15;

    // Declarative provers
    const PROVER_METAMATH: c_int  = 16;
    const PROVER_MIZAR: c_int     = 17;
    const PROVER_PVS: c_int       = 18;
    const PROVER_ACL2: c_int      = 19;
    const PROVER_TLAPS: c_int     = 20;
    const PROVER_TWELF: c_int     = 21;
    const PROVER_IMANDRA: c_int   = 22;

    // Auto-active verifiers
    const PROVER_DAFNY: c_int     = 23;
    const PROVER_WHY3: c_int      = 24;

    // Constraint solvers
    const PROVER_GLPK: c_int      = 25;
    const PROVER_SCIP: c_int      = 26;
    const PROVER_MINIZINC: c_int  = 27;
    const PROVER_CHUFFED: c_int   = 28;
    const PROVER_ORTOOLS: c_int   = 29;

    // Category constants
    const CATEGORY_INTERACTIVE: c_int  = 0;
    const CATEGORY_SMT: c_int          = 1;
    const CATEGORY_ATP: c_int          = 2;
    const CATEGORY_DECLARATIVE: c_int  = 3;
    const CATEGORY_AUTOACTIVE: c_int   = 4;
    const CATEGORY_CONSTRAINT: c_int   = 5;
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

// Allocate a null-terminated C string from a Chapel string
proc chapelToCString(s: string): c_ptrConst(c_char) {
    const len = s.size;
    var ptr = allocate(c_char, len + 1);
    for i in 0..<len {
        ptr[i] = s.byte(i):c_char;
    }
    ptr[len] = 0:c_char;
    return ptr;
}

// Convert a ProverCategory to a C int
proc categoryToInt(cat: ProverCategory): c_int {
    select cat {
        when ProverCategory.InteractiveAssistant do return CATEGORY_INTERACTIVE;
        when ProverCategory.SmtSolver            do return CATEGORY_SMT;
        when ProverCategory.FirstOrderAtp        do return CATEGORY_ATP;
        when ProverCategory.DeclarativeProver    do return CATEGORY_DECLARATIVE;
        when ProverCategory.AutoActive           do return CATEGORY_AUTOACTIVE;
        when ProverCategory.ConstraintSolver     do return CATEGORY_CONSTRAINT;
    }
    return -1:c_int;
}

// Convert a ProofResult to a C-compatible CProofResult
proc toCResult(ref chapelResult: ProofResult): CProofResult {
    var cResult: CProofResult;

    cResult.success = if chapelResult.success then 1:c_int else 0:c_int;
    cResult.prover_id = chapelResult.proverId:c_int;
    cResult.prover_name = chapelToCString(chapelResult.prover);
    cResult.time_seconds = chapelResult.time:c_double;
    cResult.exit_code = chapelResult.exitCode:c_int;
    cResult.tactic_count = 0:c_int; // Reserved
    cResult.category = categoryToInt(chapelResult.category);

    if chapelResult.success {
        cResult.error_message = nil;
    } else {
        cResult.error_message = chapelToCString(chapelResult.output);
    }

    return cResult;
}

// ---------------------------------------------------------------------------
// FFI exports
// ---------------------------------------------------------------------------

// Free a CProofResult's heap-allocated strings
export proc chapel_free_result(ref result: CProofResult) {
    if result.prover_name != nil {
        deallocate(result.prover_name);
        result.prover_name = nil;
    }
    if result.error_message != nil {
        deallocate(result.error_message);
        result.error_message = nil;
    }
}

// Main FFI export: Parallel proof search across all 30 backends.
//
// Parameters:
//   goal_cstr:    C string containing the theorem/goal to prove
//   prover_ids:   Array of prover IDs to use (or NULL for all 30)
//   num_provers:  Number of entries in prover_ids (or 0 for all 30)
//   timeout_secs: Per-prover timeout in seconds (0 = use default 300s)
//
// Returns:
//   CProofResult with the best successful proof, or failure details.
//   Caller MUST call chapel_free_result() to free allocated strings.
export proc chapel_parallel_search(
    goal_cstr: c_ptrConst(c_char),
    prover_ids: c_ptr(c_int),
    num_provers: c_int,
    timeout_secs: c_int
): CProofResult {

    // Convert C string to Chapel string
    var goal: string;
    try {
        goal = createStringWithNewBuffer(goal_cstr);
    } catch {
        var errResult: CProofResult;
        errResult.success = 0;
        errResult.prover_id = -1;
        errResult.prover_name = nil;
        errResult.time_seconds = 0.0;
        errResult.exit_code = -2;
        errResult.tactic_count = 0;
        errResult.category = -1;
        errResult.error_message = chapelToCString("Invalid goal string");
        return errResult;
    }

    var timeout = if timeout_secs > 0 then timeout_secs:int else defaultTimeout;
    var allProvers = buildProverRegistry();

    // Filter to requested provers (or use all 30)
    if num_provers > 0 && prover_ids != nil {
        var filtered: list(ProverInfo);
        for i in 0..<num_provers {
            const pid = prover_ids[i]:int;
            if pid >= 0 && pid < 30 {
                filtered.pushBack(allProvers[pid]);
            }
        }
        const chapelResult = parallelProofSearch(goal, filtered.toArray(), timeout);
        return toCResult(chapelResult);
    } else {
        const chapelResult = parallelProofSearch(goal, allProvers, timeout);
        return toCResult(chapelResult);
    }
}

// Query: Check if Chapel runtime is initialised and available
// Returns: 1 if available, 0 if not
export proc chapel_is_available(): c_int {
    return 1:c_int;
}

// Query: Get version string
// Returns: Static C string (do not free)
export proc chapel_get_version(): c_ptrConst(c_char) {
    return "ECHIDNA Chapel Metalayer v2.0.0 (30 provers)\0".c_str();
}

// Query: Get number of available provers (those found on PATH)
export proc chapel_available_prover_count(): c_int {
    var allProvers = buildProverRegistry();
    var count = 0;
    for p in allProvers {
        if isProverAvailable(p) then count += 1;
    }
    return count:c_int;
}

// Query: Check if a specific prover is available
export proc chapel_is_prover_available(prover_id: c_int): c_int {
    if prover_id < 0 || prover_id >= 30 then return 0:c_int;
    var allProvers = buildProverRegistry();
    return if isProverAvailable(allProvers[prover_id:int]) then 1:c_int else 0:c_int;
}
