// SPDX-License-Identifier: PMPL-1.0-or-later
// Chapel FFI Exports for ECHIDNA
// Provides C-compatible interface for Zig FFI layer to call

use CTypes;
use parallel_proof_search; // Import the main PoC module

// C-compatible proof result (fixed-size strings for C interop)
extern record CProofResult {
    var success: c_int;           // 0 = false, 1 = true
    var prover_name: c_ptrConst(c_char); // Prover name (allocated by Chapel)
    var time_seconds: c_double;    // Proof time in seconds
    var tactic_count: c_int;       // Number of tactics used
    var error_message: c_ptrConst(c_char); // Error if failed (NULL if success)
}

// C-compatible prover kind enum (matches Zig's ProverKind)
extern "C" {
    const PROVER_COQ: c_int = 0;
    const PROVER_LEAN: c_int = 1;
    const PROVER_ISABELLE: c_int = 2;
    const PROVER_AGDA: c_int = 3;
    const PROVER_Z3: c_int = 4;
    const PROVER_CVC5: c_int = 5;
    const PROVER_ACL2: c_int = 6;
    const PROVER_PVS: c_int = 7;
    const PROVER_HOL4: c_int = 8;
    const PROVER_METAMATH: c_int = 9;
    const PROVER_HOLLIGHT: c_int = 10;
    const PROVER_MIZAR: c_int = 11;
}

// Convert Chapel ProofResult to C-compatible structure
proc toCResult(ref chapelResult: ProofResult): CProofResult {
    var cResult: CProofResult;

    cResult.success = if chapelResult.success then 1:c_int else 0:c_int;

    // Allocate C string for prover name (caller must free)
    const nameLen = chapelResult.prover.size;
    var namePtr = allocate(c_char, nameLen + 1);
    for i in 0..<nameLen {
        namePtr[i] = chapelResult.prover.byte(i):c_char;
    }
    namePtr[nameLen] = 0:c_char; // null terminator
    cResult.prover_name = namePtr;

    cResult.time_seconds = chapelResult.time:c_double;
    cResult.tactic_count = chapelResult.tactics:c_int;

    // Error message (NULL for success)
    if chapelResult.success {
        cResult.error_message = nil;
    } else {
        const errMsg = "Proof search failed";
        const errLen = errMsg.size;
        var errPtr = allocate(c_char, errLen + 1);
        for i in 0..<errLen {
            errPtr[i] = errMsg.byte(i):c_char;
        }
        errPtr[errLen] = 0:c_char;
        cResult.error_message = errPtr;
    }

    return cResult;
}

// Free C-allocated strings in CProofResult
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

// Main FFI export: Parallel proof search callable from Zig/Rust
//
// Parameters:
//   goal_cstr: C string containing the theorem to prove
//   prover_ids: Array of prover IDs to use (or NULL for all 12)
//   num_provers: Number of provers in array (or 0 for all)
//
// Returns:
//   CProofResult with success/failure and proof details
//   Caller must call chapel_free_result() to free allocated strings
export proc chapel_parallel_search(
    goal_cstr: c_ptrConst(c_char),
    prover_ids: c_ptr(c_int),
    num_provers: c_int
): CProofResult {

    // Convert C string to Chapel string
    var goal: string;
    try {
        goal = createStringWithNewBuffer(goal_cstr);
    } catch {
        // Invalid UTF-8 or NULL pointer
        var errResult: CProofResult;
        errResult.success = 0;
        errResult.prover_name = nil;
        errResult.time_seconds = 0.0;
        errResult.tactic_count = 0;

        const errMsg = "Invalid goal string";
        const errLen = errMsg.size;
        var errPtr = allocate(c_char, errLen + 1);
        for i in 0..<errLen {
            errPtr[i] = errMsg.byte(i):c_char;
        }
        errPtr[errLen] = 0:c_char;
        errResult.error_message = errPtr;

        return errResult;
    }

    // Build prover list (default: all 12)
    var provers: [1..12] string;
    if num_provers > 0 && prover_ids != nil {
        // Use specified provers
        const proverNames = ["Coq", "Lean", "Isabelle", "Agda", "Z3", "CVC5",
                            "ACL2", "PVS", "HOL4", "Metamath", "HOL Light", "Mizar"];

        for i in 0..<num_provers {
            const proverId = prover_ids[i]:int;
            if proverId >= 0 && proverId < 12 {
                provers[i+1] = proverNames[proverId];
            }
        }
    } else {
        // Use all provers (default)
        provers = ["Coq", "Lean", "Isabelle", "Agda", "Z3", "CVC5",
                   "ACL2", "PVS", "HOL4", "Metamath", "HOL Light", "Mizar"];
    }

    // Call Chapel's parallel proof search
    const chapelResult = parallelProofSearch(goal, provers);

    // Convert to C-compatible result
    return toCResult(chapelResult);
}

// Query: Check if Chapel runtime is initialized and available
// Returns: 1 if available, 0 if not
export proc chapel_is_available(): c_int {
    return 1:c_int;  // If we can call this, Chapel is available
}

// Query: Get version string
// Returns: Static C string (do not free)
export proc chapel_get_version(): c_ptrConst(c_char) {
    return "ECHIDNA Chapel Metalayer v1.0.0\0".c_str();
}
