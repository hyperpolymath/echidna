/* SPDX-License-Identifier: PMPL-1.0-or-later
 * Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
 *
 * ECHIDNA Core FFI — C Header (generated from Idris2 ABI / Zig FFI)
 *
 * Declares the C-ABI surface of libechidna_ffi.so for external consumers
 * (V-lang adapters, other language bindings).
 *
 * Source: ffi/zig/src/main.zig
 * ABI:    src/abi/ (Idris2 definitions)
 *
 * DO NOT EDIT — regenerate from the Zig FFI source.
 */

#ifndef ECHIDNA_FFI_H
#define ECHIDNA_FFI_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ======================================================================
 * Enums
 * ====================================================================== */

/** Status codes returned by FFI functions. */
typedef enum {
    ECHIDNA_OK                        =   0,
    ECHIDNA_ERROR_INVALID_HANDLE      =  -1,
    ECHIDNA_ERROR_INVALID_ARGUMENT    =  -2,
    ECHIDNA_ERROR_PROVER_NOT_FOUND    =  -3,
    ECHIDNA_ERROR_PARSE_FAILURE       =  -4,
    ECHIDNA_ERROR_TACTIC_FAILURE      =  -5,
    ECHIDNA_ERROR_VERIFICATION_FAILURE = -6,
    ECHIDNA_ERROR_OUT_OF_MEMORY       =  -7,
    ECHIDNA_ERROR_TIMEOUT             =  -8,
    ECHIDNA_ERROR_NOT_IMPLEMENTED     =  -9,
    ECHIDNA_ERROR_UNKNOWN             = -99
} EchidnaStatus;

/** Prover kind — all 30 backends across 8 tiers. */
typedef enum {
    /* Tier 1 */
    ECHIDNA_PROVER_AGDA      =  0,
    ECHIDNA_PROVER_COQ       =  1,
    ECHIDNA_PROVER_LEAN      =  2,
    ECHIDNA_PROVER_ISABELLE   =  3,
    ECHIDNA_PROVER_Z3        =  4,
    ECHIDNA_PROVER_CVC5      =  5,

    /* Tier 2 */
    ECHIDNA_PROVER_METAMATH   =  6,
    ECHIDNA_PROVER_HOL_LIGHT  =  7,
    ECHIDNA_PROVER_MIZAR      =  8,

    /* Tier 3 */
    ECHIDNA_PROVER_PVS        =  9,
    ECHIDNA_PROVER_ACL2       = 10,

    /* Tier 4 */
    ECHIDNA_PROVER_HOL4       = 11,
    ECHIDNA_PROVER_IDRIS2     = 12,

    /* Tier 5: First-Order ATPs */
    ECHIDNA_PROVER_VAMPIRE    = 13,
    ECHIDNA_PROVER_EPROVER    = 14,
    ECHIDNA_PROVER_SPASS      = 15,
    ECHIDNA_PROVER_ALT_ERGO   = 16,

    /* Tier 6 */
    ECHIDNA_PROVER_FSTAR      = 17,
    ECHIDNA_PROVER_DAFNY      = 18,
    ECHIDNA_PROVER_WHY3       = 19,

    /* Tier 7 */
    ECHIDNA_PROVER_TLAPS      = 20,
    ECHIDNA_PROVER_TWELF      = 21,
    ECHIDNA_PROVER_NUPRL      = 22,
    ECHIDNA_PROVER_MINLOG     = 23,
    ECHIDNA_PROVER_IMANDRA    = 24,

    /* Tier 8: Constraint solvers */
    ECHIDNA_PROVER_GLPK       = 25,
    ECHIDNA_PROVER_SCIP       = 26,
    ECHIDNA_PROVER_MINIZINC   = 27,
    ECHIDNA_PROVER_CHUFFED    = 28,
    ECHIDNA_PROVER_ORTOOLS    = 29
} EchidnaProverKind;

/** Tactic result kind. */
typedef enum {
    ECHIDNA_TACTIC_SUCCESS = 0,
    ECHIDNA_TACTIC_ERROR   = 1,
    ECHIDNA_TACTIC_QED     = 2
} EchidnaTacticResultKind;

/** Term kind. */
typedef enum {
    ECHIDNA_TERM_VARIABLE       =  0,
    ECHIDNA_TERM_CONSTANT       =  1,
    ECHIDNA_TERM_APP            =  2,
    ECHIDNA_TERM_LAMBDA         =  3,
    ECHIDNA_TERM_PI             =  4,
    ECHIDNA_TERM_TYPE_UNIVERSE  =  5,
    ECHIDNA_TERM_SORT           =  6,
    ECHIDNA_TERM_LET_BINDING    =  7,
    ECHIDNA_TERM_MATCH_EXPR     =  8,
    ECHIDNA_TERM_FIX            =  9,
    ECHIDNA_TERM_HOLE           = 10,
    ECHIDNA_TERM_META           = 11,
    ECHIDNA_TERM_PROVER_SPECIFIC = 12
} EchidnaTermKind;

/** Tactic kind. */
typedef enum {
    ECHIDNA_TACTIC_APPLY       = 0,
    ECHIDNA_TACTIC_INTRO       = 1,
    ECHIDNA_TACTIC_CASES       = 2,
    ECHIDNA_TACTIC_INDUCTION   = 3,
    ECHIDNA_TACTIC_REWRITE     = 4,
    ECHIDNA_TACTIC_SIMPLIFY    = 5,
    ECHIDNA_TACTIC_REFLEXIVITY = 6,
    ECHIDNA_TACTIC_ASSUMPTION  = 7,
    ECHIDNA_TACTIC_EXACT       = 8,
    ECHIDNA_TACTIC_CUSTOM      = 9
} EchidnaTacticKind;

/* ======================================================================
 * Structs (repr(C) layout — matches Zig/Rust)
 * ====================================================================== */

/** Non-owning string slice. */
typedef struct {
    const uint8_t *ptr;
    size_t         len;
} EchidnaStringSlice;

/** Owned string — must be freed via the allocator that created it. */
typedef struct {
    uint8_t *ptr;
    size_t   len;
    size_t   capacity;
} EchidnaOwnedString;

/* ======================================================================
 * Lifecycle
 * ====================================================================== */

/** Initialise the ECHIDNA FFI layer. Returns 0 on success. */
int echidna_init(void);

/** Shut down the ECHIDNA FFI layer. */
void echidna_deinit(void);

/* ======================================================================
 * Prover management
 * ====================================================================== */

/** Create a prover. Returns handle ID (>= 0) on success, -1 on error. */
int echidna_create_prover(int kind);

/** Destroy a prover instance. */
void echidna_destroy_prover(int handle);

/** Parse a proof file. Returns 0 on success. */
int echidna_parse_file(int handle, const uint8_t *path_ptr, size_t path_len);

/** Parse a proof string. Returns 0 on success. */
int echidna_parse_string(int handle, const uint8_t *content_ptr, size_t content_len);

/** Apply a tactic. Returns 0 on success. */
int echidna_apply_tactic(int handle, const uint8_t *tactic_ptr, size_t tactic_len);

/** Verify the current proof. Returns 1 (valid), 0 (invalid), or negative on error. */
int echidna_verify_proof(int handle);

/** Export proof into buffer. Returns 0 on success, negative if buffer too small. */
int echidna_export_proof(int handle, uint8_t *out_ptr, size_t *out_len);

/** Suggest tactics into buffer. Returns 0 on success. */
int echidna_suggest_tactics(int handle, int limit, uint8_t *out_ptr, size_t *out_len);

/* ======================================================================
 * Informational
 * ====================================================================== */

/** Return library version (null-terminated, static lifetime). */
const char *echidna_version(void);

/** Return total number of supported provers (30). */
int echidna_prover_count(void);

/** Return human-readable prover name (null-terminated, static lifetime). */
const char *echidna_prover_name(int kind);

/** Return last error message (null-terminated, thread-local). NULL if no error. */
const char *echidna_last_error(void);

/** Return build information string (null-terminated, static lifetime). */
const char *echidna_build_info(void);

/* ======================================================================
 * Callback types
 * ====================================================================== */

/** Init/deinit state change callback: old_state (0=uninit,1=init), new_state. */
typedef void (*echidna_on_init_change_fn)(int old_state, int new_state);

/** Prover create/destroy callback: handle_id, prover_kind, created (1=created,0=destroyed). */
typedef void (*echidna_on_prover_change_fn)(int handle_id, int prover_kind, int created);

/** FFI error callback: error_code, msg_ptr, msg_len. */
typedef void (*echidna_on_ffi_error_fn)(int error_code, const uint8_t *msg_ptr, size_t msg_len);

/** Verify complete callback: handle_id, prover_kind, verified (1=true,0=false). */
typedef void (*echidna_on_verify_complete_fn)(int handle_id, int prover_kind, int verified);

/* ======================================================================
 * Callback registration
 * ====================================================================== */

/** Register callback for init/deinit state changes. Pass NULL to unregister. */
int echidna_register_on_init_change(echidna_on_init_change_fn callback);

/** Register callback for prover create/destroy events. Pass NULL to unregister. */
int echidna_register_on_prover_change(echidna_on_prover_change_fn callback);

/** Register callback for FFI errors. Pass NULL to unregister. */
int echidna_register_on_error(echidna_on_ffi_error_fn callback);

/** Register callback for verification completion. Pass NULL to unregister. */
int echidna_register_on_verify_complete(echidna_on_verify_complete_fn callback);

/** Unregister all callbacks. Returns 0. */
int echidna_unregister_all_callbacks(void);

/** Get number of registered callbacks (0-4). */
int echidna_callback_count(void);

#ifdef __cplusplus
}
#endif

#endif /* ECHIDNA_FFI_H */
