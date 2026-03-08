/* SPDX-License-Identifier: PMPL-1.0-or-later
 * Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
 *
 * ECHIDNA BoJ Client FFI — C Header (generated from Idris2 ABI / Zig FFI)
 *
 * Declares the C-ABI surface of libechidna_boj.so for external consumers.
 * Provides cartridge management and service discovery for the BoJ runtime.
 *
 * Source: ffi/zig/src/boj.zig
 * ABI:    src/abi/BojForeign.idr
 *
 * DO NOT EDIT — regenerate from the Zig FFI source.
 */

#ifndef ECHIDNA_BOJ_H
#define ECHIDNA_BOJ_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ======================================================================
 * Enums
 * ====================================================================== */

/** Cartridge lifecycle status. */
typedef enum {
    ECHIDNA_CARTRIDGE_DEVELOPMENT = 0,
    ECHIDNA_CARTRIDGE_READY       = 1,
    ECHIDNA_CARTRIDGE_DEPRECATED  = 2,
    ECHIDNA_CARTRIDGE_FAULTY      = 3
} EchidnaCartridgeStatus;

/** Protocol types supported by cartridges. */
typedef enum {
    ECHIDNA_PROTOCOL_MCP     = 0,
    ECHIDNA_PROTOCOL_LSP     = 1,
    ECHIDNA_PROTOCOL_DAP     = 2,
    ECHIDNA_PROTOCOL_BSP     = 3,
    ECHIDNA_PROTOCOL_NESY    = 4,
    ECHIDNA_PROTOCOL_AGENTIC = 5,
    ECHIDNA_PROTOCOL_FLEET   = 6,
    ECHIDNA_PROTOCOL_GRPC    = 7,
    ECHIDNA_PROTOCOL_REST    = 8
} EchidnaProtocolType;

/** Capability domains. */
typedef enum {
    ECHIDNA_DOMAIN_CLOUD     =  0,
    ECHIDNA_DOMAIN_CONTAINER =  1,
    ECHIDNA_DOMAIN_DATABASE  =  2,
    ECHIDNA_DOMAIN_K8S       =  3,
    ECHIDNA_DOMAIN_GIT       =  4,
    ECHIDNA_DOMAIN_SECRETS   =  5,
    ECHIDNA_DOMAIN_QUEUES    =  6,
    ECHIDNA_DOMAIN_IAC       =  7,
    ECHIDNA_DOMAIN_OBSERVE   =  8,
    ECHIDNA_DOMAIN_SSG       =  9,
    ECHIDNA_DOMAIN_PROOF     = 10,
    ECHIDNA_DOMAIN_FLEET     = 11,
    ECHIDNA_DOMAIN_NESY      = 12,
    ECHIDNA_DOMAIN_AGENT     = 13
} EchidnaCapabilityDomain;

/** BoJ connection status. */
typedef enum {
    ECHIDNA_BOJ_DISCONNECTED = 0,
    ECHIDNA_BOJ_CONNECTING   = 1,
    ECHIDNA_BOJ_CONNECTED    = 2,
    ECHIDNA_BOJ_ERROR        = 3
} EchidnaBojConnectionStatus;

/** BoJ error codes (-200 to -299). */
typedef enum {
    ECHIDNA_BOJ_OK                 =    0,
    ECHIDNA_BOJ_NOT_CONNECTED      = -200,
    ECHIDNA_BOJ_SERVER_UNAVAILABLE = -201,
    ECHIDNA_BOJ_CARTRIDGE_NOT_FOUND = -202,
    ECHIDNA_BOJ_CARTRIDGE_NOT_READY = -203,
    ECHIDNA_BOJ_INVOKE_FAILED      = -204,
    ECHIDNA_BOJ_INVALID_ARGUMENT   = -205,
    ECHIDNA_BOJ_BUFFER_TOO_SMALL   = -206,
    ECHIDNA_BOJ_TIMEOUT            = -207,
    ECHIDNA_BOJ_UNKNOWN            = -299
} EchidnaBojError;

/* ======================================================================
 * Callback types
 * ====================================================================== */

/** Status change callback: old_status, new_status. */
typedef void (*echidna_boj_on_status_change_fn)(int old_status, int new_status);

/** Cartridge change callback: name_ptr, name_len, loaded (1=loaded, 0=unloaded). */
typedef void (*echidna_boj_on_cartridge_change_fn)(const uint8_t *name_ptr, size_t name_len, int loaded);

/** Invoke complete callback: name_ptr, name_len, tool_ptr, tool_len, result_code. */
typedef void (*echidna_boj_on_invoke_complete_fn)(const uint8_t *name_ptr, size_t name_len, const uint8_t *tool_ptr, size_t tool_len, int result_code);

/* ======================================================================
 * Connection
 * ====================================================================== */

/** Connect to BoJ server. config: connection string. Returns 0 on success. */
int echidna_boj_connect(const uint8_t *config_ptr, size_t config_len);

/** Disconnect from BoJ server. */
void echidna_boj_disconnect(void);

/** Get BoJ connection status. */
int echidna_boj_status(void);

/** Get BoJ server health. Writes JSON to out_ptr. Returns 0 on success. */
int echidna_boj_health(uint8_t *out_ptr, size_t *out_len);

/* ======================================================================
 * Cartridge management
 * ====================================================================== */

/** List all cartridges. Writes JSON array to out_ptr. Returns 0 on success. */
int echidna_boj_list_cartridges(uint8_t *out_ptr, size_t *out_len);

/** Get cartridge details. Writes JSON to out_ptr. Returns 0 on success. */
int echidna_boj_get_cartridge(const uint8_t *name_ptr, size_t name_len, uint8_t *out_ptr, size_t *out_len);

/** Load (mount) a cartridge. Returns 0 on success. */
int echidna_boj_load_cartridge(const uint8_t *name_ptr, size_t name_len);

/** Unload (unmount) a cartridge. Returns 0 on success. */
int echidna_boj_unload_cartridge(const uint8_t *name_ptr, size_t name_len);

/** Invoke a tool on a cartridge. Writes result JSON to out_ptr. Returns 0 on success. */
int echidna_boj_invoke(const uint8_t *name_ptr, size_t name_len,
                       const uint8_t *tool_ptr, size_t tool_len,
                       const uint8_t *args_ptr, size_t args_len,
                       uint8_t *out_ptr, size_t *out_len);

/* ======================================================================
 * Topology and federation
 * ====================================================================== */

/** Get topology matrix. Writes JSON to out_ptr. Returns 0 on success. */
int echidna_boj_topology(uint8_t *out_ptr, size_t *out_len);

/** Get Umoja federation status. Writes JSON to out_ptr. Returns 0 on success. */
int echidna_boj_umoja_status(uint8_t *out_ptr, size_t *out_len);

/** Get cartridge count. */
int echidna_boj_cartridge_count(void);

/* ======================================================================
 * Callback registration
 * ====================================================================== */

/** Register callback for BoJ status changes. Pass NULL to unregister. */
int echidna_boj_register_on_status_change(echidna_boj_on_status_change_fn callback);

/** Register callback for cartridge load/unload. Pass NULL to unregister. */
int echidna_boj_register_on_cartridge_change(echidna_boj_on_cartridge_change_fn callback);

/** Register callback for invoke completion. Pass NULL to unregister. */
int echidna_boj_register_on_invoke_complete(echidna_boj_on_invoke_complete_fn callback);

/** Unregister all BoJ callbacks. Returns 0. */
int echidna_boj_unregister_all_callbacks(void);

/** Get number of registered BoJ callbacks (0-3). */
int echidna_boj_callback_count(void);

/* ======================================================================
 * Unified
 * ====================================================================== */

/** Return BoJ client version (null-terminated, static lifetime). */
const char *echidna_boj_version(void);

/** Return last BoJ error (null-terminated, thread-local). NULL if no error. */
const char *echidna_boj_last_error(void);

#ifdef __cplusplus
}
#endif

#endif /* ECHIDNA_BOJ_H */
