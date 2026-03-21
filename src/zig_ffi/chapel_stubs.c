/* SPDX-License-Identifier: PMPL-1.0-or-later */
/* Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
 *
 * Stub implementations of Chapel FFI exports for building/testing
 * without the Chapel runtime. These return "unavailable" gracefully.
 */

#include "chapel_ffi_exports.h"
#include <stdlib.h>
#include <string.h>

CProofResult chapel_parallel_search(
    const char *goal,
    const int *prover_ids,
    int num_provers,
    int timeout_secs
) {
    (void)goal;
    (void)prover_ids;
    (void)num_provers;
    (void)timeout_secs;
    CProofResult result = {0};
    result.success = 0;
    result.prover_id = -1;
    result.prover_name = NULL;
    result.time_seconds = 0.0;
    result.exit_code = -1;
    result.tactic_count = 0;
    result.error_message = strdup("Chapel runtime not available (stub)");
    result.category = -1;
    return result;
}

void chapel_free_result(CProofResult *result) {
    if (result) {
        free((void *)result->prover_name);
        free((void *)result->error_message);
        result->prover_name = NULL;
        result->error_message = NULL;
    }
}

int chapel_is_available(void) {
    return 0; /* Not available in stub mode */
}

const char *chapel_get_version(void) {
    return NULL; /* No version in stub mode */
}

int chapel_available_prover_count(void) {
    return 0; /* No provers in stub mode */
}

int chapel_is_prover_available(int prover_id) {
    (void)prover_id;
    return 0; /* No provers in stub mode */
}

void chapel_free_string(const char *str) {
    free((void *)str);
}
