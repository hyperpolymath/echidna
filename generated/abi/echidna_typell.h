/* SPDX-License-Identifier: PMPL-1.0-or-later
 * Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
 *
 * ECHIDNA TypeLL Client FFI — C Header (generated from Idris2 ABI / Zig FFI)
 *
 * Declares the C-ABI surface of libechidna_typell.so for external consumers.
 * Provides type checking, inference, refinement, and type-level computation.
 *
 * Source: ffi/zig/src/typell.zig
 * ABI:    src/abi/TypeLLForeign.idr
 *
 * DO NOT EDIT — regenerate from the Zig FFI source.
 */

#ifndef ECHIDNA_TYPELL_H
#define ECHIDNA_TYPELL_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ======================================================================
 * Enums
 * ====================================================================== */

/** Type universe levels. */
typedef enum {
    ECHIDNA_UNIVERSE_TYPE0 = 0,  /**< Type : Type₀ */
    ECHIDNA_UNIVERSE_TYPE1 = 1,  /**< Type₀ : Type₁ */
    ECHIDNA_UNIVERSE_TYPE2 = 2,  /**< Type₁ : Type₂ */
    ECHIDNA_UNIVERSE_OMEGA = 3   /**< Typeω (universe polymorphism) */
} EchidnaUniverse;

/** Type checking result kinds. */
typedef enum {
    ECHIDNA_CHECK_WELL_TYPED             = 0,
    ECHIDNA_CHECK_TYPE_MISMATCH          = 1,
    ECHIDNA_CHECK_UNBOUND_VARIABLE       = 2,
    ECHIDNA_CHECK_UNIVERSE_INCONSISTENCY = 3,
    ECHIDNA_CHECK_OCCURS_CHECK_FAILED    = 4,
    ECHIDNA_CHECK_AMBIGUOUS              = 5
} EchidnaCheckResult;

/** TypeLL connection status. */
typedef enum {
    ECHIDNA_TYPELL_DISCONNECTED = 0,
    ECHIDNA_TYPELL_CONNECTING   = 1,
    ECHIDNA_TYPELL_CONNECTED    = 2,
    ECHIDNA_TYPELL_ERROR        = 3
} EchidnaTypeLLConnectionStatus;

/** TypeLL error codes (-300 to -399). */
typedef enum {
    ECHIDNA_TYPELL_OK               =    0,
    ECHIDNA_TYPELL_NOT_CONNECTED    = -300,
    ECHIDNA_TYPELL_TYPE_ERROR       = -301,
    ECHIDNA_TYPELL_PARSE_ERROR      = -302,
    ECHIDNA_TYPELL_INVALID_ARGUMENT = -303,
    ECHIDNA_TYPELL_BUFFER_TOO_SMALL = -304,
    ECHIDNA_TYPELL_TIMEOUT          = -305,
    ECHIDNA_TYPELL_NOT_IMPLEMENTED  = -306,
    ECHIDNA_TYPELL_UNKNOWN          = -399
} EchidnaTypeLLError;

/* ======================================================================
 * Callback types
 * ====================================================================== */

/** Status change callback: old_status, new_status. */
typedef void (*echidna_typell_on_status_change_fn)(int old_status, int new_status);

/** Check complete callback: result (CheckResult enum), msg_ptr, msg_len. */
typedef void (*echidna_typell_on_check_complete_fn)(int result, const uint8_t *msg_ptr, size_t msg_len);

/* ======================================================================
 * Connection
 * ====================================================================== */

/** Connect to TypeLL server. config: connection string. Returns 0 on success. */
int echidna_typell_connect(const uint8_t *config_ptr, size_t config_len);

/** Disconnect from TypeLL server. */
void echidna_typell_disconnect(void);

/** Get TypeLL connection status. */
int echidna_typell_status(void);

/** Get TypeLL server health. Writes JSON to out_ptr. Returns 0 on success. */
int echidna_typell_health(uint8_t *out_ptr, size_t *out_len);

/* ======================================================================
 * Type operations
 * ====================================================================== */

/** Type-check an expression with context. Writes result JSON to out_ptr. Returns 0 on success. */
int echidna_typell_check(const uint8_t *expr_ptr, size_t expr_len,
                         const uint8_t *ctx_ptr, size_t ctx_len,
                         uint8_t *out_ptr, size_t *out_len);

/** Infer the type of an expression. Writes result JSON to out_ptr. Returns 0 on success. */
int echidna_typell_infer(const uint8_t *expr_ptr, size_t expr_len,
                         uint8_t *out_ptr, size_t *out_len);

/** Apply refinement types to a specification. Writes result JSON to out_ptr. Returns 0 on success. */
int echidna_typell_refine(const uint8_t *spec_ptr, size_t spec_len,
                          const uint8_t *constraints_ptr, size_t constraints_len,
                          uint8_t *out_ptr, size_t *out_len);

/** Evaluate a type-level computation. Writes result JSON to out_ptr. Returns 0 on success. */
int echidna_typell_compute(const uint8_t *term_ptr, size_t term_len,
                           uint8_t *out_ptr, size_t *out_len);

/** List available type signatures. Writes JSON array to out_ptr. Returns 0 on success. */
int echidna_typell_list_signatures(uint8_t *out_ptr, size_t *out_len);

/** Get type universe hierarchy. Writes JSON to out_ptr. Returns 0 on success. */
int echidna_typell_universes(uint8_t *out_ptr, size_t *out_len);

/* ======================================================================
 * Callback registration
 * ====================================================================== */

/** Register callback for TypeLL status changes. Pass NULL to unregister. */
int echidna_typell_register_on_status_change(echidna_typell_on_status_change_fn callback);

/** Register callback for type check completion. Pass NULL to unregister. */
int echidna_typell_register_on_check_complete(echidna_typell_on_check_complete_fn callback);

/** Unregister all TypeLL callbacks. Returns 0. */
int echidna_typell_unregister_all_callbacks(void);

/** Get number of registered TypeLL callbacks (0-2). */
int echidna_typell_callback_count(void);

/* ======================================================================
 * Unified
 * ====================================================================== */

/** Return TypeLL client version (null-terminated, static lifetime). */
const char *echidna_typell_version(void);

/** Return last TypeLL error (null-terminated, thread-local). NULL if no error. */
const char *echidna_typell_last_error(void);

#ifdef __cplusplus
}
#endif

#endif /* ECHIDNA_TYPELL_H */
