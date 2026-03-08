/* SPDX-License-Identifier: PMPL-1.0-or-later
 * Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
 *
 * ECHIDNA Tentacles FFI — C Header (generated from Idris2 ABI / Zig FFI)
 *
 * Declares the C-ABI surface of libechidna_tentacles.so for external consumers.
 * Provides compiler agent management, task dispatch, OODA tracking, and events.
 *
 * Source: ffi/zig/src/tentacles.zig
 * ABI:    src/abi/TentaclesForeign.idr
 *
 * DO NOT EDIT — regenerate from the Zig FFI source.
 */

#ifndef ECHIDNA_TENTACLES_H
#define ECHIDNA_TENTACLES_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ======================================================================
 * Enums
 * ====================================================================== */

/** Tentacle agent colour identifier. */
typedef enum {
    ECHIDNA_TENTACLE_RED    = 0,
    ECHIDNA_TENTACLE_ORANGE = 1,
    ECHIDNA_TENTACLE_YELLOW = 2,
    ECHIDNA_TENTACLE_GREEN  = 3,
    ECHIDNA_TENTACLE_BLUE   = 4,
    ECHIDNA_TENTACLE_INDIGO = 5,
    ECHIDNA_TENTACLE_VIOLET = 6
} EchidnaTentacleId;

/** OODA loop phase. */
typedef enum {
    ECHIDNA_OODA_OBSERVE = 0,
    ECHIDNA_OODA_ORIENT  = 1,
    ECHIDNA_OODA_DECIDE  = 2,
    ECHIDNA_OODA_ACT     = 3
} EchidnaOodaPhase;

/** Progressive reveal stage. */
typedef enum {
    ECHIDNA_STAGE_CUTTLE   = 0,
    ECHIDNA_STAGE_SQUIDLET = 1,
    ECHIDNA_STAGE_DUET     = 2,
    ECHIDNA_STAGE_OCTOPUS  = 3
} EchidnaTentacleStage;

/** Agent runtime status. */
typedef enum {
    ECHIDNA_AGENT_IDLE     = 0,
    ECHIDNA_AGENT_BUSY     = 1,
    ECHIDNA_AGENT_ERROR    = 2,
    ECHIDNA_AGENT_DISABLED = 3
} EchidnaAgentStatus;

/** Tentacles error codes (-300 to -399). */
typedef enum {
    ECHIDNA_TENTACLES_OK              =    0,
    ECHIDNA_TENTACLES_NOT_INIT        = -300,
    ECHIDNA_TENTACLES_INVALID_AGENT   = -301,
    ECHIDNA_TENTACLES_AGENT_BUSY      = -302,
    ECHIDNA_TENTACLES_AGENT_ERROR     = -303,
    ECHIDNA_TENTACLES_TASK_FAILED     = -304,
    ECHIDNA_TENTACLES_INVALID_STAGE   = -305,
    ECHIDNA_TENTACLES_BUFFER_TOO_SMALL = -306,
    ECHIDNA_TENTACLES_BROADCAST_FAILED = -307,
    ECHIDNA_TENTACLES_UNKNOWN         = -399
} EchidnaTentaclesError;

/* ======================================================================
 * Callback types
 * ====================================================================== */

/** Phase change callback: agent_id, old_phase, new_phase. */
typedef void (*echidna_tentacles_on_phase_change_fn)(int agent_id, int old_phase, int new_phase);

/** Task complete callback: agent_id, result_code (0=success, -1=cancelled, <0=error). */
typedef void (*echidna_tentacles_on_task_complete_fn)(int agent_id, int result_code);

/** Error callback: agent_id, error_code, msg_ptr, msg_len. */
typedef void (*echidna_tentacles_on_error_fn)(int agent_id, int error_code, const uint8_t *msg_ptr, size_t msg_len);

/* ======================================================================
 * Initialisation
 * ====================================================================== */

/** Initialise the tentacles system. Returns 0 on success. */
int echidna_tentacles_init(void);

/** Shut down the tentacles system. */
void echidna_tentacles_shutdown(void);

/* ======================================================================
 * Agent queries
 * ====================================================================== */

/** Get agent status. Returns AgentStatus enum value or error code. */
int echidna_tentacles_agent_status(int agent_id);

/** Get agent's current OODA phase. Returns OodaPhase enum value or error code. */
int echidna_tentacles_agent_phase(int agent_id);

/** Get agent's current stage. Returns TentacleStage enum value or error code. */
int echidna_tentacles_agent_stage(int agent_id);

/* ======================================================================
 * Task dispatch
 * ====================================================================== */

/** Dispatch a task to an agent. task_ptr/task_len is a UTF-8 task description. Returns 0 on success. */
int echidna_tentacles_dispatch_task(int agent_id, const uint8_t *task_ptr, size_t task_len);

/** Cancel an agent's current task. Returns 0 on success. */
int echidna_tentacles_cancel_task(int agent_id);

/* ======================================================================
 * Stage management
 * ====================================================================== */

/** Set the global reveal stage for all agents. Returns 0 on success. */
int echidna_tentacles_set_global_stage(int stage_id);

/** Get the current global stage. Returns TentacleStage enum value. */
int echidna_tentacles_get_global_stage(void);

/* ======================================================================
 * Event polling
 * ====================================================================== */

/** Poll agent states as JSON array. Writes to out_ptr. Returns 0 on success. */
int echidna_tentacles_poll_events(uint8_t *out_ptr, size_t *out_len);

/** Get count of busy agents. */
int echidna_tentacles_event_count(void);

/* ======================================================================
 * Broadcast
 * ====================================================================== */

/** Record a broadcast from an agent. payload is JSON. Returns 0 on success. */
int echidna_tentacles_broadcast(int source_id, const uint8_t *payload_ptr, size_t payload_len);

/* ======================================================================
 * Callback registration
 * ====================================================================== */

/** Register callback for OODA phase changes. Pass NULL to unregister. */
int echidna_tentacles_register_on_phase_change(echidna_tentacles_on_phase_change_fn callback);

/** Register callback for task completion. Pass NULL to unregister. */
int echidna_tentacles_register_on_task_complete(echidna_tentacles_on_task_complete_fn callback);

/** Register callback for agent errors. Pass NULL to unregister. */
int echidna_tentacles_register_on_error(echidna_tentacles_on_error_fn callback);

/** Unregister all tentacles callbacks. Returns 0. */
int echidna_tentacles_unregister_all_callbacks(void);

/** Get number of registered callbacks (0-3). */
int echidna_tentacles_callback_count(void);

/* ======================================================================
 * Unified
 * ====================================================================== */

/** Return tentacles version (null-terminated, static lifetime). */
const char *echidna_tentacles_version(void);

/** Return last error (null-terminated, thread-local). NULL if no error. */
const char *echidna_tentacles_last_error(void);

/** Return total agent count (always 7). */
int echidna_tentacles_agent_count(void);

#ifdef __cplusplus
}
#endif

#endif /* ECHIDNA_TENTACLES_H */
