/* SPDX-License-Identifier: PMPL-1.0-or-later */
/* ECHIDNA Chapel FFI Exports — C header interface
 *
 * This header defines the C ABI that Chapel's `export` functions provide.
 * When Chapel is compiled, it generates compatible symbols.
 * When Chapel is NOT available, stub implementations return "unavailable".
 *
 * The Zig bridge (@cImport) imports this header and wraps it type-safely.
 */

#ifndef ECHIDNA_CHAPEL_FFI_EXPORTS_H
#define ECHIDNA_CHAPEL_FFI_EXPORTS_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* C-compatible proof result from Chapel's parallel search */
typedef struct {
    int success;           /* 0 = false, 1 = true */
    int prover_id;         /* ProverKind enum value (-1 if unknown) */
    double time_seconds;
    uint32_t tactic_count;
    const char *prover_name;    /* NULL or heap-allocated string */
    const char *error_message;  /* NULL or heap-allocated string */
} CProofResult;

/* Main entry point: parallel proof search across all Chapel-managed provers.
 * goal:        null-terminated theorem statement
 * prover_ids:  array of prover IDs to use (NULL = all provers)
 * num_provers: length of prover_ids (0 = all provers)
 * Returns:     CProofResult (caller must free via chapel_free_result) */
CProofResult chapel_parallel_search(
    const char *goal,
    const int *prover_ids,
    int num_provers
);

/* Free a CProofResult returned by chapel_parallel_search */
void chapel_free_result(CProofResult *result);

/* Check if Chapel runtime is available (returns 1 if yes, 0 if no) */
int chapel_is_available(void);

/* Get Chapel metalayer version string (caller must free via chapel_free_string) */
const char *chapel_get_version(void);

/* Free a string returned by chapel_get_version */
void chapel_free_string(const char *str);

#ifdef __cplusplus
}
#endif

#endif /* ECHIDNA_CHAPEL_FFI_EXPORTS_H */
