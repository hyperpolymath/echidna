/* SPDX-License-Identifier: PMPL-1.0-or-later
 * Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
 *
 * ECHIDNA Overlay Network FFI — C Header (generated from Idris2 ABI / Zig FFI)
 *
 * Declares the C-ABI surface of libechidna_overlay.so for external consumers.
 * Covers Tor, IPFS, and Ethereum overlay network integrations.
 *
 * Source: ffi/zig/src/overlay.zig
 * ABI:    src/abi/OverlayForeign.idr
 *
 * DO NOT EDIT — regenerate from the Zig FFI source.
 */

#ifndef ECHIDNA_OVERLAY_H
#define ECHIDNA_OVERLAY_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ======================================================================
 * Enums
 * ====================================================================== */

/** Overlay network kind. */
typedef enum {
    ECHIDNA_OVERLAY_TOR      = 0,
    ECHIDNA_OVERLAY_IPFS     = 1,
    ECHIDNA_OVERLAY_ETHEREUM = 2
} EchidnaOverlayKind;

/** Overlay connection status. */
typedef enum {
    ECHIDNA_OVERLAY_DISCONNECTED = 0,
    ECHIDNA_OVERLAY_CONNECTING   = 1,
    ECHIDNA_OVERLAY_CONNECTED    = 2,
    ECHIDNA_OVERLAY_ERROR        = 3
} EchidnaOverlayStatus;

/** Tor circuit status. */
typedef enum {
    ECHIDNA_TOR_CIRCUIT_BUILDING = 0,
    ECHIDNA_TOR_CIRCUIT_BUILT    = 1,
    ECHIDNA_TOR_CIRCUIT_CLOSED   = 2,
    ECHIDNA_TOR_CIRCUIT_FAILED   = 3
} EchidnaTorCircuitStatus;

/** IPFS pin status. */
typedef enum {
    ECHIDNA_IPFS_PINNED     = 0,
    ECHIDNA_IPFS_UNPINNED   = 1,
    ECHIDNA_IPFS_PIN_QUEUED = 2,
    ECHIDNA_IPFS_PIN_FAILED = 3
} EchidnaIpfsPinStatus;

/** Ethereum network. */
typedef enum {
    ECHIDNA_ETH_MAINNET = 0,
    ECHIDNA_ETH_SEPOLIA = 1,
    ECHIDNA_ETH_HOLESKY = 2,
    ECHIDNA_ETH_LOCAL   = 3
} EchidnaEthNetwork;

/** Overlay error codes (-100 to -199). */
typedef enum {
    ECHIDNA_OVERLAY_OK                =    0,
    ECHIDNA_OVERLAY_NOT_CONNECTED     = -100,
    ECHIDNA_OVERLAY_CONNECTION_REFUSED = -101,
    ECHIDNA_OVERLAY_TIMEOUT           = -102,
    ECHIDNA_OVERLAY_INVALID_ARGUMENT  = -103,
    ECHIDNA_OVERLAY_NOT_FOUND         = -104,
    ECHIDNA_OVERLAY_BUFFER_TOO_SMALL  = -105,
    ECHIDNA_OVERLAY_DAEMON_NOT_RUNNING = -106,
    ECHIDNA_OVERLAY_AUTH_FAILED       = -107,
    ECHIDNA_OVERLAY_NOT_IMPLEMENTED   = -108,
    ECHIDNA_OVERLAY_UNKNOWN           = -199
} EchidnaOverlayError;

/* ======================================================================
 * Callback types
 * ====================================================================== */

/** Status change callback: kind (0=Tor,1=IPFS,2=Eth), old_status, new_status. */
typedef void (*echidna_overlay_on_status_change_fn)(int kind, int old_status, int new_status);

/** Error callback: kind, error_code, msg_ptr, msg_len. */
typedef void (*echidna_overlay_on_error_fn)(int kind, int error_code, const uint8_t *msg_ptr, size_t msg_len);

/** Progress callback: kind, operation_id, bytes_done, bytes_total. */
typedef void (*echidna_overlay_on_progress_fn)(int kind, int operation_id, uint64_t bytes_done, uint64_t bytes_total);

/** Tor circuit change callback: circuit_id, old_status, new_status. */
typedef void (*echidna_overlay_on_circuit_change_fn)(int circuit_id, int old_status, int new_status);

/** IPFS pin change callback: cid_ptr, cid_len, old_status, new_status. */
typedef void (*echidna_overlay_on_pin_change_fn)(const uint8_t *cid_ptr, size_t cid_len, int old_status, int new_status);

/* ======================================================================
 * Tor
 * ====================================================================== */

/** Connect to Tor control port. config: JSON. Returns 0 on success. */
int echidna_tor_connect(const uint8_t *config_ptr, size_t config_len);

/** Disconnect from Tor. */
void echidna_tor_disconnect(void);

/** Create a hidden service. Writes .onion address to out_ptr. Returns 0 on success. */
int echidna_tor_create_hidden_service(int port, int target_port, uint8_t *out_ptr, size_t *out_len);

/** Destroy a hidden service by .onion address. Returns 0 on success. */
int echidna_tor_destroy_hidden_service(const uint8_t *onion_ptr, size_t onion_len);

/** Get circuit information by ID. Writes JSON to out_ptr. Returns 0 on success. */
int echidna_tor_get_circuit(int circuit_id, uint8_t *out_ptr, size_t *out_len);

/** List all active circuits. Writes JSON array to out_ptr. Returns 0 on success. */
int echidna_tor_list_circuits(uint8_t *out_ptr, size_t *out_len);

/** Resolve hostname through Tor SOCKS5. Writes IP to out_ptr. Returns 0 on success. */
int echidna_tor_resolve(const uint8_t *hostname_ptr, size_t hostname_len, uint8_t *out_ptr, size_t *out_len);

/** Get Tor connection status. */
int echidna_tor_status(void);

/** Get count of active hidden services. */
int echidna_tor_hidden_service_count(void);

/* ======================================================================
 * IPFS
 * ====================================================================== */

/** Connect to IPFS HTTP RPC API. config: JSON. Returns 0 on success. */
int echidna_ipfs_connect(const uint8_t *config_ptr, size_t config_len);

/** Disconnect from IPFS. */
void echidna_ipfs_disconnect(void);

/** Add content to IPFS. Writes CID to out_cid_ptr. Returns 0 on success. */
int echidna_ipfs_add(const uint8_t *data_ptr, size_t data_len, uint8_t *out_cid_ptr, size_t *out_cid_len);

/** Retrieve content by CID. Writes content to out_ptr. Returns 0 on success. */
int echidna_ipfs_cat(const uint8_t *cid_ptr, size_t cid_len, uint8_t *out_ptr, size_t *out_len);

/** Pin content on IPFS. Returns 0 on success. */
int echidna_ipfs_pin(const uint8_t *cid_ptr, size_t cid_len);

/** Unpin content from IPFS. Returns 0 on success. */
int echidna_ipfs_unpin(const uint8_t *cid_ptr, size_t cid_len);

/** Get IPFS DAG node. Writes JSON to out_ptr. Returns 0 on success. */
int echidna_ipfs_dag_get(const uint8_t *cid_ptr, size_t cid_len, uint8_t *out_ptr, size_t *out_len);

/** Get IPFS connection status. */
int echidna_ipfs_status(void);

/** Get count of pinned items. */
int echidna_ipfs_pin_count(void);

/* ======================================================================
 * Ethereum
 * ====================================================================== */

/** Connect to Ethereum JSON-RPC. config: JSON. Returns 0 on success. */
int echidna_eth_connect(const uint8_t *config_ptr, size_t config_len);

/** Disconnect from Ethereum. */
void echidna_eth_disconnect(void);

/** Timestamp a proof hash on-chain. Writes JSON result to out_ptr. Returns 0 on success. */
int echidna_eth_timestamp_proof(const uint8_t *proof_hash_ptr, size_t proof_hash_len, uint8_t *out_ptr, size_t *out_len);

/** Verify a previously timestamped proof. Writes JSON to out_ptr. Returns 0 on success. */
int echidna_eth_verify_timestamp(const uint8_t *tx_hash_ptr, size_t tx_hash_len, uint8_t *out_ptr, size_t *out_len);

/** Get Ethereum connection status. */
int echidna_eth_status(void);

/* ======================================================================
 * Callback registration
 * ====================================================================== */

/** Register callback for overlay status changes. Pass NULL to unregister. */
int echidna_overlay_register_on_status_change(echidna_overlay_on_status_change_fn callback);

/** Register callback for overlay errors. Pass NULL to unregister. */
int echidna_overlay_register_on_error(echidna_overlay_on_error_fn callback);

/** Register callback for progress events. Pass NULL to unregister. */
int echidna_overlay_register_on_progress(echidna_overlay_on_progress_fn callback);

/** Register callback for Tor circuit changes. Pass NULL to unregister. */
int echidna_overlay_register_on_circuit_change(echidna_overlay_on_circuit_change_fn callback);

/** Register callback for IPFS pin changes. Pass NULL to unregister. */
int echidna_overlay_register_on_pin_change(echidna_overlay_on_pin_change_fn callback);

/** Unregister all callbacks. Returns 0. */
int echidna_overlay_unregister_all_callbacks(void);

/** Get number of registered callbacks (0-5). */
int echidna_overlay_callback_count(void);

/* ======================================================================
 * Unified
 * ====================================================================== */

/** Return overlay module version (null-terminated, static lifetime). */
const char *echidna_overlay_version(void);

/** Return overlay kind name (null-terminated, static lifetime). */
const char *echidna_overlay_kind_name(int kind);

/** Return last overlay error (null-terminated, thread-local). NULL if no error. */
const char *echidna_overlay_last_error(void);

#ifdef __cplusplus
}
#endif

#endif /* ECHIDNA_OVERLAY_H */
