/* SPDX-License-Identifier: PMPL-1.0-or-later */
/* Stub implementations of Chapel FFI exports for testing/building
 * without the Chapel runtime. These return "unavailable" gracefully. */

#include "chapel_ffi_exports.h"
#include <stdlib.h>
#include <string.h>

CProofResult chapel_parallel_search(
    const char *goal,
    const int *prover_ids,
    int num_provers
) {
    (void)goal;
    (void)prover_ids;
    (void)num_provers;
    CProofResult result = {0};
    result.success = 0;
    result.prover_id = -1;
    result.time_seconds = 0.0;
    result.tactic_count = 0;
    result.prover_name = NULL;
    result.error_message = strdup("Chapel runtime not available (stub)");
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

void chapel_free_string(const char *str) {
    free((void *)str);
}
