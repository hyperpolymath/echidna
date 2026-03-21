/* SPDX-License-Identifier: PMPL-1.0-or-later */
/* Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
 *
 * ECHIDNA Chapel FFI Exports — C header interface (30 provers)
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

/* -------------------------------------------------------------------------
 * Prover ID constants — all 30 ECHIDNA backends
 * Must match ProverKind in Zig and ProverInfo.id in Chapel.
 * ------------------------------------------------------------------------- */

/* Interactive proof assistants (10) */
#define PROVER_AGDA      0
#define PROVER_COQ       1
#define PROVER_LEAN      2
#define PROVER_ISABELLE  3
#define PROVER_IDRIS2    4
#define PROVER_FSTAR     5
#define PROVER_HOL4      6
#define PROVER_HOLLIGHT  7
#define PROVER_NUPRL     8
#define PROVER_MINLOG    9

/* SMT solvers (3) */
#define PROVER_Z3        10
#define PROVER_CVC5      11
#define PROVER_ALTERGO   12

/* First-order ATPs (3) */
#define PROVER_VAMPIRE   13
#define PROVER_EPROVER   14
#define PROVER_SPASS     15

/* Declarative provers (7) */
#define PROVER_METAMATH  16
#define PROVER_MIZAR     17
#define PROVER_PVS       18
#define PROVER_ACL2      19
#define PROVER_TLAPS     20
#define PROVER_TWELF     21
#define PROVER_IMANDRA   22

/* Auto-active verifiers (2) */
#define PROVER_DAFNY     23
#define PROVER_WHY3      24

/* Constraint solvers (5) */
#define PROVER_GLPK      25
#define PROVER_SCIP      26
#define PROVER_MINIZINC  27
#define PROVER_CHUFFED   28
#define PROVER_ORTOOLS   29

#define PROVER_COUNT     30

/* Prover category constants */
#define CATEGORY_INTERACTIVE  0
#define CATEGORY_SMT          1
#define CATEGORY_ATP          2
#define CATEGORY_DECLARATIVE  3
#define CATEGORY_AUTOACTIVE   4
#define CATEGORY_CONSTRAINT   5

/* -------------------------------------------------------------------------
 * C-compatible proof result from Chapel's parallel search
 * ------------------------------------------------------------------------- */

typedef struct {
    int success;               /* 0 = false, 1 = true */
    int prover_id;             /* ProverInfo.id (-1 if unknown) */
    const char *prover_name;   /* NULL or heap-allocated string */
    double time_seconds;
    int exit_code;             /* Subprocess exit code */
    int tactic_count;          /* Reserved for future use */
    const char *error_message; /* NULL or heap-allocated string */
    int category;              /* CATEGORY_* constant */
} CProofResult;

/* -------------------------------------------------------------------------
 * Main entry point: parallel proof search across Chapel-managed provers.
 *
 * goal:          null-terminated theorem statement
 * prover_ids:    array of PROVER_* IDs to use (NULL = all 30 provers)
 * num_provers:   length of prover_ids (0 = all 30 provers)
 * timeout_secs:  per-prover timeout in seconds (0 = default 300s)
 *
 * Returns: CProofResult (caller must free via chapel_free_result)
 * ------------------------------------------------------------------------- */
CProofResult chapel_parallel_search(
    const char *goal,
    const int *prover_ids,
    int num_provers,
    int timeout_secs
);

/* Free a CProofResult returned by chapel_parallel_search */
void chapel_free_result(CProofResult *result);

/* Check if Chapel runtime is available (returns 1 if yes, 0 if no) */
int chapel_is_available(void);

/* Get Chapel metalayer version string (static — do NOT free) */
const char *chapel_get_version(void);

/* Get number of provers available on this system (0-30) */
int chapel_available_prover_count(void);

/* Check if a specific prover is available (returns 1/0) */
int chapel_is_prover_available(int prover_id);

/* Free a string returned by chapel_get_version (no-op for static) */
void chapel_free_string(const char *str);

#ifdef __cplusplus
}
#endif

#endif /* ECHIDNA_CHAPEL_FFI_EXPORTS_H */
