// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

/**
 * @file echidna_ffi.h
 * @brief ECHIDNA FFI Bridge Layer - C Header
 *
 * This header provides C-compatible declarations for integrating
 * ECHIDNA's theorem proving capabilities with external systems.
 *
 * Supported languages:
 * - Rust (via bindgen or manual FFI)
 * - Idris 2 (via foreign function interface)
 * - Julia (via ccall)
 * - Any C-compatible language
 */

#ifndef ECHIDNA_FFI_H
#define ECHIDNA_FFI_H

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

// ============================================================================
// Type Definitions
// ============================================================================

/** Opaque handle to a prover instance */
typedef void* EchidnaProverHandle;

/** Opaque handle to a proof state */
typedef void* EchidnaProofStateHandle;

/** Opaque handle to a term */
typedef void* EchidnaTermHandle;

/** Prover kind enumeration */
typedef enum {
    ECHIDNA_PROVER_AGDA = 0,
    ECHIDNA_PROVER_COQ = 1,
    ECHIDNA_PROVER_LEAN = 2,
    ECHIDNA_PROVER_ISABELLE = 3,
    ECHIDNA_PROVER_Z3 = 4,
    ECHIDNA_PROVER_CVC5 = 5,
    ECHIDNA_PROVER_METAMATH = 6,
    ECHIDNA_PROVER_HOLLIGHT = 7,
    ECHIDNA_PROVER_MIZAR = 8,
    ECHIDNA_PROVER_PVS = 9,
    ECHIDNA_PROVER_ACL2 = 10,
    ECHIDNA_PROVER_HOL4 = 11,
    ECHIDNA_PROVER_IDRIS2 = 12,
} EchidnaProverKind;

/** Status codes */
typedef enum {
    ECHIDNA_OK = 0,
    ECHIDNA_ERROR_INVALID_HANDLE = -1,
    ECHIDNA_ERROR_INVALID_ARGUMENT = -2,
    ECHIDNA_ERROR_PROVER_NOT_FOUND = -3,
    ECHIDNA_ERROR_PARSE_FAILURE = -4,
    ECHIDNA_ERROR_TACTIC_FAILURE = -5,
    ECHIDNA_ERROR_VERIFICATION_FAILURE = -6,
    ECHIDNA_ERROR_OUT_OF_MEMORY = -7,
    ECHIDNA_ERROR_TIMEOUT = -8,
    ECHIDNA_ERROR_NOT_IMPLEMENTED = -9,
    ECHIDNA_ERROR_UNKNOWN = -99,
} EchidnaStatus;

/** Tactic result kind */
typedef enum {
    ECHIDNA_TACTIC_SUCCESS = 0,
    ECHIDNA_TACTIC_ERROR = 1,
    ECHIDNA_TACTIC_QED = 2,
} EchidnaTacticResultKind;

/** Term kind */
typedef enum {
    ECHIDNA_TERM_VAR = 0,
    ECHIDNA_TERM_CONST = 1,
    ECHIDNA_TERM_APP = 2,
    ECHIDNA_TERM_LAMBDA = 3,
    ECHIDNA_TERM_PI = 4,
    ECHIDNA_TERM_TYPE = 5,
    ECHIDNA_TERM_SORT = 6,
    ECHIDNA_TERM_LET = 7,
    ECHIDNA_TERM_MATCH = 8,
    ECHIDNA_TERM_FIX = 9,
    ECHIDNA_TERM_HOLE = 10,
    ECHIDNA_TERM_META = 11,
    ECHIDNA_TERM_PROVER_SPECIFIC = 12,
} EchidnaTermKind;

/** Tactic kind */
typedef enum {
    ECHIDNA_TACTIC_APPLY = 0,
    ECHIDNA_TACTIC_INTRO = 1,
    ECHIDNA_TACTIC_CASES = 2,
    ECHIDNA_TACTIC_INDUCTION = 3,
    ECHIDNA_TACTIC_REWRITE = 4,
    ECHIDNA_TACTIC_SIMPLIFY = 5,
    ECHIDNA_TACTIC_REFLEXIVITY = 6,
    ECHIDNA_TACTIC_ASSUMPTION = 7,
    ECHIDNA_TACTIC_EXACT = 8,
    ECHIDNA_TACTIC_CUSTOM = 9,
} EchidnaTacticKind;

/** Non-owning string slice */
typedef struct {
    const uint8_t* ptr;
    size_t len;
} EchidnaStringSlice;

/** Owned string (must be freed with echidna_string_free) */
typedef struct {
    uint8_t* ptr;
    size_t len;
    size_t capacity;
} EchidnaOwnedString;

/** Prover configuration */
typedef struct {
    EchidnaStringSlice executable_path;
    EchidnaStringSlice* library_paths;
    size_t library_paths_len;
    uint64_t timeout_ms;
    bool neural_enabled;
    uint8_t _padding[7];
} EchidnaProverConfig;

/** Serialized term */
typedef struct {
    EchidnaTermKind kind;
    uint8_t _padding[3];
    uint32_t data_len;
    const uint8_t* data;
} EchidnaSerializedTerm;

/** Goal */
typedef struct {
    EchidnaStringSlice id;
    EchidnaSerializedTerm target;
    uint32_t hypotheses_count;
    uint8_t _padding[4];
} EchidnaGoal;

/** Tactic */
typedef struct {
    EchidnaTacticKind kind;
    uint8_t _padding[3];
    uint32_t arg_len;
    const uint8_t* arg;
} EchidnaTactic;

/** Tactic result */
typedef struct {
    EchidnaTacticResultKind kind;
    uint8_t _padding[3];
    uint32_t message_len;
    const uint8_t* message;
    EchidnaProofStateHandle new_state;
} EchidnaTacticResult;

/** Proof obligation (for bulletproof-core integration) */
typedef struct {
    EchidnaStringSlice name;
    EchidnaSerializedTerm statement;
    uint32_t context_len;
    uint8_t _padding[4];
} EchidnaProofObligation;

/** Verification result */
typedef struct {
    bool valid;
    uint8_t _padding1[3];
    uint32_t message_len;
    const uint8_t* message;
    EchidnaTermHandle proof_term;
} EchidnaVerificationResult;

// ============================================================================
// Lifecycle Functions
// ============================================================================

/**
 * Initialize the ECHIDNA FFI layer.
 * Must be called before any other functions.
 *
 * @return ECHIDNA_OK on success
 */
EchidnaStatus echidna_init(void);

/**
 * Shutdown the ECHIDNA FFI layer and release all resources.
 *
 * @return ECHIDNA_OK on success
 */
EchidnaStatus echidna_shutdown(void);

// ============================================================================
// Prover Management
// ============================================================================

/**
 * Create a new prover instance.
 *
 * @param kind The prover type to create
 * @param config Configuration for the prover
 * @param out_handle Output parameter for the prover handle
 * @return ECHIDNA_OK on success
 */
EchidnaStatus echidna_prover_create(
    EchidnaProverKind kind,
    const EchidnaProverConfig* config,
    EchidnaProverHandle* out_handle
);

/**
 * Destroy a prover instance.
 *
 * @param handle The prover handle to destroy
 * @return ECHIDNA_OK on success
 */
EchidnaStatus echidna_prover_destroy(EchidnaProverHandle handle);

/**
 * Get the version string of a prover.
 *
 * @param handle The prover handle
 * @param out_version Output parameter for the version string (must be freed)
 * @return ECHIDNA_OK on success
 */
EchidnaStatus echidna_prover_version(
    EchidnaProverHandle handle,
    EchidnaOwnedString* out_version
);

// ============================================================================
// Parsing
// ============================================================================

/**
 * Parse a proof file.
 *
 * @param handle The prover handle
 * @param path Path to the proof file
 * @param out_state Output parameter for the proof state
 * @return ECHIDNA_OK on success
 */
EchidnaStatus echidna_parse_file(
    EchidnaProverHandle handle,
    EchidnaStringSlice path,
    EchidnaProofStateHandle* out_state
);

/**
 * Parse a proof from a string.
 *
 * @param handle The prover handle
 * @param content The proof content
 * @param out_state Output parameter for the proof state
 * @return ECHIDNA_OK on success
 */
EchidnaStatus echidna_parse_string(
    EchidnaProverHandle handle,
    EchidnaStringSlice content,
    EchidnaProofStateHandle* out_state
);

// ============================================================================
// Tactics
// ============================================================================

/**
 * Apply a tactic to a proof state.
 *
 * @param handle The prover handle
 * @param state The current proof state
 * @param tactic The tactic to apply
 * @param out_result Output parameter for the result
 * @return ECHIDNA_OK on success
 */
EchidnaStatus echidna_apply_tactic(
    EchidnaProverHandle handle,
    EchidnaProofStateHandle state,
    const EchidnaTactic* tactic,
    EchidnaTacticResult* out_result
);

/**
 * Get suggested tactics for the current proof state.
 *
 * @param handle The prover handle
 * @param state The current proof state
 * @param limit Maximum number of suggestions
 * @param out_tactics Output array for tactics
 * @param out_count Output parameter for the number of suggestions
 * @return ECHIDNA_OK on success
 */
EchidnaStatus echidna_suggest_tactics(
    EchidnaProverHandle handle,
    EchidnaProofStateHandle state,
    uint32_t limit,
    EchidnaTactic* out_tactics,
    uint32_t* out_count
);

// ============================================================================
// Verification
// ============================================================================

/**
 * Verify a proof state.
 *
 * @param handle The prover handle
 * @param state The proof state to verify
 * @param out_valid Output parameter for validity
 * @return ECHIDNA_OK on success
 */
EchidnaStatus echidna_verify_proof(
    EchidnaProverHandle handle,
    EchidnaProofStateHandle state,
    bool* out_valid
);

/**
 * Export a proof to prover-specific format.
 *
 * @param handle The prover handle
 * @param state The proof state to export
 * @param out_content Output parameter for the exported content
 * @return ECHIDNA_OK on success
 */
EchidnaStatus echidna_export_proof(
    EchidnaProverHandle handle,
    EchidnaProofStateHandle state,
    EchidnaOwnedString* out_content
);

// ============================================================================
// Term Construction
// ============================================================================

EchidnaStatus echidna_term_var(EchidnaStringSlice name, EchidnaTermHandle* out_term);
EchidnaStatus echidna_term_const(EchidnaStringSlice name, EchidnaTermHandle* out_term);
EchidnaStatus echidna_term_app(
    EchidnaTermHandle func,
    const EchidnaTermHandle* args,
    size_t args_len,
    EchidnaTermHandle* out_term
);
EchidnaStatus echidna_term_lambda(
    EchidnaStringSlice param,
    EchidnaTermHandle param_type,
    EchidnaTermHandle body,
    EchidnaTermHandle* out_term
);
EchidnaStatus echidna_term_pi(
    EchidnaStringSlice param,
    EchidnaTermHandle param_type,
    EchidnaTermHandle body,
    EchidnaTermHandle* out_term
);
EchidnaStatus echidna_term_type(uint32_t level, EchidnaTermHandle* out_term);
EchidnaStatus echidna_term_hole(EchidnaStringSlice name, EchidnaTermHandle* out_term);
EchidnaStatus echidna_term_free(EchidnaTermHandle term);

// ============================================================================
// Proof State Queries
// ============================================================================

EchidnaStatus echidna_state_goal_count(EchidnaProofStateHandle state, uint32_t* out_count);
EchidnaStatus echidna_state_get_goal(
    EchidnaProofStateHandle state,
    uint32_t index,
    EchidnaGoal* out_goal
);
EchidnaStatus echidna_state_is_complete(EchidnaProofStateHandle state, bool* out_complete);
EchidnaStatus echidna_state_free(EchidnaProofStateHandle state);

// ============================================================================
// Memory Management
// ============================================================================

/**
 * Free an owned string.
 *
 * @param str The string to free
 */
void echidna_string_free(EchidnaOwnedString* str);

/**
 * Allocate memory.
 *
 * @param size Number of bytes to allocate
 * @return Pointer to allocated memory, or NULL on failure
 */
uint8_t* echidna_alloc(size_t size);

/**
 * Free allocated memory.
 *
 * @param ptr Pointer to memory to free
 * @param size Size of the allocation
 */
void echidna_free(uint8_t* ptr, size_t size);

// ============================================================================
// Bulletproof-Core Integration
// ============================================================================

/**
 * Submit a proof obligation from bulletproof-core for verification.
 *
 * @param prover The prover to use
 * @param obligation The proof obligation
 * @param out_result Output parameter for the verification result
 * @return ECHIDNA_OK on success
 */
EchidnaStatus echidna_bulletproof_verify(
    EchidnaProverKind prover,
    const EchidnaProofObligation* obligation,
    EchidnaVerificationResult* out_result
);

/**
 * Request neural tactic suggestions for a bulletproof-core proof.
 *
 * @param prover The prover to use
 * @param obligation The proof obligation
 * @param limit Maximum number of suggestions
 * @param out_tactics Output array for tactics
 * @param out_count Output parameter for the number of suggestions
 * @return ECHIDNA_OK on success
 */
EchidnaStatus echidna_bulletproof_suggest(
    EchidnaProverKind prover,
    const EchidnaProofObligation* obligation,
    uint32_t limit,
    EchidnaTactic* out_tactics,
    uint32_t* out_count
);

// ============================================================================
// Callback Registration
// ============================================================================

/** Callback function types */
typedef EchidnaStatus (*EchidnaParseFileCallback)(
    EchidnaProverKind, EchidnaStringSlice, EchidnaProofStateHandle*
);
typedef EchidnaStatus (*EchidnaParseStringCallback)(
    EchidnaProverKind, EchidnaStringSlice, EchidnaProofStateHandle*
);
typedef EchidnaStatus (*EchidnaApplyTacticCallback)(
    EchidnaProverKind, EchidnaProofStateHandle, const EchidnaTactic*, EchidnaTacticResult*
);
typedef EchidnaStatus (*EchidnaVerifyProofCallback)(
    EchidnaProverKind, EchidnaProofStateHandle, bool*
);
typedef EchidnaStatus (*EchidnaExportProofCallback)(
    EchidnaProverKind, EchidnaProofStateHandle, EchidnaOwnedString*
);
typedef EchidnaStatus (*EchidnaSuggestTacticsCallback)(
    EchidnaProverKind, EchidnaProofStateHandle, uint32_t, EchidnaTactic*, uint32_t*
);

/**
 * Register callbacks from the Rust side.
 *
 * @param parse_file Callback for file parsing
 * @param parse_string Callback for string parsing
 * @param apply_tactic Callback for tactic application
 * @param verify_proof Callback for proof verification
 * @param export_proof Callback for proof export
 * @param suggest_tactics Callback for tactic suggestions
 * @return ECHIDNA_OK on success
 */
EchidnaStatus echidna_register_callbacks(
    EchidnaParseFileCallback parse_file,
    EchidnaParseStringCallback parse_string,
    EchidnaApplyTacticCallback apply_tactic,
    EchidnaVerifyProofCallback verify_proof,
    EchidnaExportProofCallback export_proof,
    EchidnaSuggestTacticsCallback suggest_tactics
);

// ============================================================================
// Utility Macros
// ============================================================================

/** Create a string slice from a C string literal */
#define ECHIDNA_STR(s) ((EchidnaStringSlice){ .ptr = (const uint8_t*)(s), .len = sizeof(s) - 1 })

/** Create an empty string slice */
#define ECHIDNA_STR_EMPTY ((EchidnaStringSlice){ .ptr = NULL, .len = 0 })

#ifdef __cplusplus
}
#endif

#endif /* ECHIDNA_FFI_H */
