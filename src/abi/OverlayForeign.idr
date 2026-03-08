-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- ECHIDNA Overlay ABI Foreign Function Declarations
--
-- Declares all C-compatible functions exported by the overlay FFI layer
-- (ffi/zig/src/overlay.zig) for Tor, IPFS, and Ethereum overlay networks.
--
-- Every FFI function has:
--   1. A raw PrimIO declaration matching the C symbol
--   2. A safe Idris2 wrapper with proper error handling
--   3. Return type mapped to OverlayStatus or Int (0 = success, negative = error)
--
-- NO believe_me anywhere. All safety is enforced by types.

module Overlay.Foreign

import Overlay

%default total

--------------------------------------------------------------------------------
-- Helper: interpret overlay error codes
--------------------------------------------------------------------------------

||| Convert a C int return code to a success/failure result.
||| 0 = success, negative = error code from OverlayError enum.
public export
data OverlayResult : Type where
  OverlayOk     : OverlayResult
  OverlayFailed : (code : Int) -> OverlayResult

||| Interpret an FFI return code
public export
overlayResult : Int -> OverlayResult
overlayResult 0 = OverlayOk
overlayResult n = OverlayFailed n

||| Convert raw status int to OverlayStatus
public export
overlayStatusFromInt : Int -> OverlayStatus
overlayStatusFromInt 0 = OverlayDisconnected
overlayStatusFromInt 1 = OverlayConnecting
overlayStatusFromInt 2 = OverlayConnected
overlayStatusFromInt _ = OverlayError "unknown"

||| String helper (reuse from Foreign.idr pattern)
export
%foreign "support:idris2_getString, libidris2_support"
prim__getString : Bits64 -> String

--------------------------------------------------------------------------------
-- Unified Overlay Functions
--------------------------------------------------------------------------------

||| Get overlay module version string.
||| C: const char* echidna_overlay_version(void);
export
%foreign "C:echidna_overlay_version, libechidna_overlay"
prim__overlayVersion : PrimIO Bits64

||| Safe wrapper: overlay version
export
overlayVersion : IO String
overlayVersion = do
  ptr <- primIO prim__overlayVersion
  pure (if ptr == 0 then "unknown" else prim__getString ptr)

||| Get overlay kind name.
||| C: const char* echidna_overlay_kind_name(int kind);
export
%foreign "C:echidna_overlay_kind_name, libechidna_overlay"
prim__overlayKindName : Int -> PrimIO Bits64

||| Safe wrapper: kind name
export
overlayKindName : OverlayKind -> IO String
overlayKindName kind = do
  ptr <- primIO (prim__overlayKindName (overlayKindToInt kind))
  pure (if ptr == 0 then "Unknown" else prim__getString ptr)

||| Get last overlay error message.
||| C: const char* echidna_overlay_last_error(void);
export
%foreign "C:echidna_overlay_last_error, libechidna_overlay"
prim__overlayLastError : PrimIO Bits64

||| Safe wrapper: last error
export
overlayLastError : IO (Maybe String)
overlayLastError = do
  ptr <- primIO prim__overlayLastError
  pure (if ptr == 0 then Nothing else Just (prim__getString ptr))

--------------------------------------------------------------------------------
-- Tor Foreign Functions
--------------------------------------------------------------------------------

||| Connect to Tor control port.
||| C: int echidna_tor_connect(const uint8_t* config_ptr, size_t config_len);
export
%foreign "C:echidna_tor_connect, libechidna_overlay"
prim__torConnect : Bits64 -> Bits64 -> PrimIO Int

||| Safe wrapper: connect to Tor
export
torConnect : (configPtr : Bits64) -> (configLen : Bits64) -> IO OverlayResult
torConnect ptr len = do
  rc <- primIO (prim__torConnect ptr len)
  pure (overlayResult rc)

||| Disconnect from Tor.
||| C: void echidna_tor_disconnect(void);
export
%foreign "C:echidna_tor_disconnect, libechidna_overlay"
prim__torDisconnect : PrimIO ()

||| Safe wrapper: disconnect from Tor
export
torDisconnect : IO ()
torDisconnect = primIO prim__torDisconnect

||| Create a Tor hidden service.
||| C: int echidna_tor_create_hidden_service(int port, int target_port, uint8_t* out_ptr, size_t* out_len);
export
%foreign "C:echidna_tor_create_hidden_service, libechidna_overlay"
prim__torCreateHiddenService : Int -> Int -> Bits64 -> Bits64 -> PrimIO Int

||| Safe wrapper: create hidden service
export
torCreateHiddenService : (port : Int) -> (targetPort : Int) -> (outPtr : Bits64) -> (outLenPtr : Bits64) -> IO OverlayResult
torCreateHiddenService port tp outPtr outLenPtr = do
  rc <- primIO (prim__torCreateHiddenService port tp outPtr outLenPtr)
  pure (overlayResult rc)

||| Destroy a Tor hidden service.
||| C: int echidna_tor_destroy_hidden_service(const uint8_t* onion_ptr, size_t onion_len);
export
%foreign "C:echidna_tor_destroy_hidden_service, libechidna_overlay"
prim__torDestroyHiddenService : Bits64 -> Bits64 -> PrimIO Int

||| Safe wrapper: destroy hidden service
export
torDestroyHiddenService : (onionPtr : Bits64) -> (onionLen : Bits64) -> IO OverlayResult
torDestroyHiddenService ptr len = do
  rc <- primIO (prim__torDestroyHiddenService ptr len)
  pure (overlayResult rc)

||| Get Tor circuit information.
||| C: int echidna_tor_get_circuit(int circuit_id, uint8_t* out_ptr, size_t* out_len);
export
%foreign "C:echidna_tor_get_circuit, libechidna_overlay"
prim__torGetCircuit : Int -> Bits64 -> Bits64 -> PrimIO Int

||| Safe wrapper: get circuit
export
torGetCircuit : (circuitId : Int) -> (outPtr : Bits64) -> (outLenPtr : Bits64) -> IO OverlayResult
torGetCircuit cid outPtr outLen = do
  rc <- primIO (prim__torGetCircuit cid outPtr outLen)
  pure (overlayResult rc)

||| List all active Tor circuits.
||| C: int echidna_tor_list_circuits(uint8_t* out_ptr, size_t* out_len);
export
%foreign "C:echidna_tor_list_circuits, libechidna_overlay"
prim__torListCircuits : Bits64 -> Bits64 -> PrimIO Int

||| Safe wrapper: list circuits
export
torListCircuits : (outPtr : Bits64) -> (outLenPtr : Bits64) -> IO OverlayResult
torListCircuits outPtr outLen = do
  rc <- primIO (prim__torListCircuits outPtr outLen)
  pure (overlayResult rc)

||| Resolve a hostname through Tor.
||| C: int echidna_tor_resolve(const uint8_t* hostname_ptr, size_t hostname_len, uint8_t* out_ptr, size_t* out_len);
export
%foreign "C:echidna_tor_resolve, libechidna_overlay"
prim__torResolve : Bits64 -> Bits64 -> Bits64 -> Bits64 -> PrimIO Int

||| Safe wrapper: resolve via Tor
export
torResolve : (hostnamePtr : Bits64) -> (hostnameLen : Bits64) -> (outPtr : Bits64) -> (outLenPtr : Bits64) -> IO OverlayResult
torResolve hPtr hLen outPtr outLen = do
  rc <- primIO (prim__torResolve hPtr hLen outPtr outLen)
  pure (overlayResult rc)

||| Get Tor connection status.
||| C: int echidna_tor_status(void);
export
%foreign "C:echidna_tor_status, libechidna_overlay"
prim__torStatus : PrimIO Int

||| Safe wrapper: Tor status
export
torStatus : IO OverlayStatus
torStatus = do
  code <- primIO prim__torStatus
  pure (overlayStatusFromInt code)

||| Get count of active hidden services.
||| C: int echidna_tor_hidden_service_count(void);
export
%foreign "C:echidna_tor_hidden_service_count, libechidna_overlay"
prim__torHiddenServiceCount : PrimIO Int

||| Safe wrapper: hidden service count
export
torHiddenServiceCount : IO Int
torHiddenServiceCount = primIO prim__torHiddenServiceCount

--------------------------------------------------------------------------------
-- IPFS Foreign Functions
--------------------------------------------------------------------------------

||| Connect to IPFS.
||| C: int echidna_ipfs_connect(const uint8_t* config_ptr, size_t config_len);
export
%foreign "C:echidna_ipfs_connect, libechidna_overlay"
prim__ipfsConnect : Bits64 -> Bits64 -> PrimIO Int

||| Safe wrapper: connect to IPFS
export
ipfsConnect : (configPtr : Bits64) -> (configLen : Bits64) -> IO OverlayResult
ipfsConnect ptr len = do
  rc <- primIO (prim__ipfsConnect ptr len)
  pure (overlayResult rc)

||| Disconnect from IPFS.
||| C: void echidna_ipfs_disconnect(void);
export
%foreign "C:echidna_ipfs_disconnect, libechidna_overlay"
prim__ipfsDisconnect : PrimIO ()

||| Safe wrapper: disconnect from IPFS
export
ipfsDisconnect : IO ()
ipfsDisconnect = primIO prim__ipfsDisconnect

||| Add content to IPFS.
||| C: int echidna_ipfs_add(const uint8_t* data_ptr, size_t data_len, uint8_t* out_cid_ptr, size_t* out_cid_len);
export
%foreign "C:echidna_ipfs_add, libechidna_overlay"
prim__ipfsAdd : Bits64 -> Bits64 -> Bits64 -> Bits64 -> PrimIO Int

||| Safe wrapper: add content to IPFS
export
ipfsAdd : (dataPtr : Bits64) -> (dataLen : Bits64) -> (outCidPtr : Bits64) -> (outCidLenPtr : Bits64) -> IO OverlayResult
ipfsAdd dPtr dLen cPtr cLen = do
  rc <- primIO (prim__ipfsAdd dPtr dLen cPtr cLen)
  pure (overlayResult rc)

||| Retrieve content from IPFS.
||| C: int echidna_ipfs_cat(const uint8_t* cid_ptr, size_t cid_len, uint8_t* out_ptr, size_t* out_len);
export
%foreign "C:echidna_ipfs_cat, libechidna_overlay"
prim__ipfsCat : Bits64 -> Bits64 -> Bits64 -> Bits64 -> PrimIO Int

||| Safe wrapper: cat content from IPFS
export
ipfsCat : (cidPtr : Bits64) -> (cidLen : Bits64) -> (outPtr : Bits64) -> (outLenPtr : Bits64) -> IO OverlayResult
ipfsCat cPtr cLen outPtr outLen = do
  rc <- primIO (prim__ipfsCat cPtr cLen outPtr outLen)
  pure (overlayResult rc)

||| Pin content on IPFS.
||| C: int echidna_ipfs_pin(const uint8_t* cid_ptr, size_t cid_len);
export
%foreign "C:echidna_ipfs_pin, libechidna_overlay"
prim__ipfsPin : Bits64 -> Bits64 -> PrimIO Int

||| Safe wrapper: pin content
export
ipfsPin : (cidPtr : Bits64) -> (cidLen : Bits64) -> IO OverlayResult
ipfsPin ptr len = do
  rc <- primIO (prim__ipfsPin ptr len)
  pure (overlayResult rc)

||| Unpin content from IPFS.
||| C: int echidna_ipfs_unpin(const uint8_t* cid_ptr, size_t cid_len);
export
%foreign "C:echidna_ipfs_unpin, libechidna_overlay"
prim__ipfsUnpin : Bits64 -> Bits64 -> PrimIO Int

||| Safe wrapper: unpin content
export
ipfsUnpin : (cidPtr : Bits64) -> (cidLen : Bits64) -> IO OverlayResult
ipfsUnpin ptr len = do
  rc <- primIO (prim__ipfsUnpin ptr len)
  pure (overlayResult rc)

||| Get IPFS DAG node.
||| C: int echidna_ipfs_dag_get(const uint8_t* cid_ptr, size_t cid_len, uint8_t* out_ptr, size_t* out_len);
export
%foreign "C:echidna_ipfs_dag_get, libechidna_overlay"
prim__ipfsDagGet : Bits64 -> Bits64 -> Bits64 -> Bits64 -> PrimIO Int

||| Safe wrapper: get DAG node
export
ipfsDagGet : (cidPtr : Bits64) -> (cidLen : Bits64) -> (outPtr : Bits64) -> (outLenPtr : Bits64) -> IO OverlayResult
ipfsDagGet cPtr cLen outPtr outLen = do
  rc <- primIO (prim__ipfsDagGet cPtr cLen outPtr outLen)
  pure (overlayResult rc)

||| Get IPFS connection status.
||| C: int echidna_ipfs_status(void);
export
%foreign "C:echidna_ipfs_status, libechidna_overlay"
prim__ipfsStatus : PrimIO Int

||| Safe wrapper: IPFS status
export
ipfsStatus : IO OverlayStatus
ipfsStatus = do
  code <- primIO prim__ipfsStatus
  pure (overlayStatusFromInt code)

||| Get count of pinned items.
||| C: int echidna_ipfs_pin_count(void);
export
%foreign "C:echidna_ipfs_pin_count, libechidna_overlay"
prim__ipfsPinCount : PrimIO Int

||| Safe wrapper: pin count
export
ipfsPinCount : IO Int
ipfsPinCount = primIO prim__ipfsPinCount

--------------------------------------------------------------------------------
-- Ethereum Foreign Functions (stubbed — Aerie future use)
--------------------------------------------------------------------------------

||| Connect to Ethereum.
||| C: int echidna_eth_connect(const uint8_t* config_ptr, size_t config_len);
export
%foreign "C:echidna_eth_connect, libechidna_overlay"
prim__ethConnect : Bits64 -> Bits64 -> PrimIO Int

||| Safe wrapper: connect to Ethereum
export
ethConnect : (configPtr : Bits64) -> (configLen : Bits64) -> IO OverlayResult
ethConnect ptr len = do
  rc <- primIO (prim__ethConnect ptr len)
  pure (overlayResult rc)

||| Disconnect from Ethereum.
||| C: void echidna_eth_disconnect(void);
export
%foreign "C:echidna_eth_disconnect, libechidna_overlay"
prim__ethDisconnect : PrimIO ()

||| Safe wrapper: disconnect from Ethereum
export
ethDisconnect : IO ()
ethDisconnect = primIO prim__ethDisconnect

||| Timestamp proof on-chain.
||| C: int echidna_eth_timestamp_proof(const uint8_t* hash_ptr, size_t hash_len, uint8_t* out_ptr, size_t* out_len);
export
%foreign "C:echidna_eth_timestamp_proof, libechidna_overlay"
prim__ethTimestampProof : Bits64 -> Bits64 -> Bits64 -> Bits64 -> PrimIO Int

||| Safe wrapper: timestamp proof
export
ethTimestampProof : (hashPtr : Bits64) -> (hashLen : Bits64) -> (outPtr : Bits64) -> (outLenPtr : Bits64) -> IO OverlayResult
ethTimestampProof hPtr hLen outPtr outLen = do
  rc <- primIO (prim__ethTimestampProof hPtr hLen outPtr outLen)
  pure (overlayResult rc)

||| Verify timestamp on-chain.
||| C: int echidna_eth_verify_timestamp(const uint8_t* tx_ptr, size_t tx_len, uint8_t* out_ptr, size_t* out_len);
export
%foreign "C:echidna_eth_verify_timestamp, libechidna_overlay"
prim__ethVerifyTimestamp : Bits64 -> Bits64 -> Bits64 -> Bits64 -> PrimIO Int

||| Safe wrapper: verify timestamp
export
ethVerifyTimestamp : (txHashPtr : Bits64) -> (txHashLen : Bits64) -> (outPtr : Bits64) -> (outLenPtr : Bits64) -> IO OverlayResult
ethVerifyTimestamp tPtr tLen outPtr outLen = do
  rc <- primIO (prim__ethVerifyTimestamp tPtr tLen outPtr outLen)
  pure (overlayResult rc)

||| Get Ethereum connection status.
||| C: int echidna_eth_status(void);
export
%foreign "C:echidna_eth_status, libechidna_overlay"
prim__ethStatus : PrimIO Int

||| Safe wrapper: Ethereum status
export
ethStatus : IO OverlayStatus
ethStatus = do
  code <- primIO prim__ethStatus
  pure (overlayStatusFromInt code)

--------------------------------------------------------------------------------
-- Callback Registration Foreign Functions (Bidirectional ABI ↔ FFI)
--------------------------------------------------------------------------------
--
-- These functions register callbacks from the ABI layer into the FFI layer.
-- The FFI invokes these callbacks on state changes, errors, and progress events.
--
-- Architecture:
--   Idris2 ABI (here) → registers callback ptr → Zig FFI stores it →
--   Zig fires callback on event → Idris2 handler runs
--
-- Callback function pointer types (C calling convention):
--   OnStatusChange: (kind: Int, old_status: Int, new_status: Int) -> ()
--   OnError:        (kind: Int, error_code: Int, msg_ptr: Ptr, msg_len: Bits64) -> ()
--   OnProgress:     (kind: Int, op_id: Int, bytes_done: Bits64, bytes_total: Bits64) -> ()
--   OnCircuitChange: (circuit_id: Int, old_status: Int, new_status: Int) -> ()
--   OnPinChange:    (cid_ptr: Ptr, cid_len: Bits64, old_status: Int, new_status: Int) -> ()

||| Register a callback for overlay status changes.
||| C: int echidna_overlay_register_on_status_change(void* callback);
||| Pass a null pointer (0) to unregister.
export
%foreign "C:echidna_overlay_register_on_status_change, libechidna_overlay"
prim__registerOnStatusChange : Bits64 -> PrimIO Int

||| Safe wrapper: register status change callback
export
registerOnStatusChange : (callbackPtr : Bits64) -> IO OverlayResult
registerOnStatusChange ptr = do
  rc <- primIO (prim__registerOnStatusChange ptr)
  pure (overlayResult rc)

||| Register a callback for overlay errors.
||| C: int echidna_overlay_register_on_error(void* callback);
export
%foreign "C:echidna_overlay_register_on_error, libechidna_overlay"
prim__registerOnError : Bits64 -> PrimIO Int

||| Safe wrapper: register error callback
export
registerOnError : (callbackPtr : Bits64) -> IO OverlayResult
registerOnError ptr = do
  rc <- primIO (prim__registerOnError ptr)
  pure (overlayResult rc)

||| Register a callback for progress events.
||| C: int echidna_overlay_register_on_progress(void* callback);
export
%foreign "C:echidna_overlay_register_on_progress, libechidna_overlay"
prim__registerOnProgress : Bits64 -> PrimIO Int

||| Safe wrapper: register progress callback
export
registerOnProgress : (callbackPtr : Bits64) -> IO OverlayResult
registerOnProgress ptr = do
  rc <- primIO (prim__registerOnProgress ptr)
  pure (overlayResult rc)

||| Register a callback for Tor circuit changes.
||| C: int echidna_overlay_register_on_circuit_change(void* callback);
export
%foreign "C:echidna_overlay_register_on_circuit_change, libechidna_overlay"
prim__registerOnCircuitChange : Bits64 -> PrimIO Int

||| Safe wrapper: register circuit change callback
export
registerOnCircuitChange : (callbackPtr : Bits64) -> IO OverlayResult
registerOnCircuitChange ptr = do
  rc <- primIO (prim__registerOnCircuitChange ptr)
  pure (overlayResult rc)

||| Register a callback for IPFS pin status changes.
||| C: int echidna_overlay_register_on_pin_change(void* callback);
export
%foreign "C:echidna_overlay_register_on_pin_change, libechidna_overlay"
prim__registerOnPinChange : Bits64 -> PrimIO Int

||| Safe wrapper: register pin change callback
export
registerOnPinChange : (callbackPtr : Bits64) -> IO OverlayResult
registerOnPinChange ptr = do
  rc <- primIO (prim__registerOnPinChange ptr)
  pure (overlayResult rc)

||| Unregister all callbacks at once.
||| C: int echidna_overlay_unregister_all_callbacks(void);
export
%foreign "C:echidna_overlay_unregister_all_callbacks, libechidna_overlay"
prim__unregisterAllCallbacks : PrimIO Int

||| Safe wrapper: unregister all callbacks
export
unregisterAllCallbacks : IO OverlayResult
unregisterAllCallbacks = do
  rc <- primIO prim__unregisterAllCallbacks
  pure (overlayResult rc)

||| Get the number of currently registered callbacks (0-5).
||| C: int echidna_overlay_callback_count(void);
export
%foreign "C:echidna_overlay_callback_count, libechidna_overlay"
prim__callbackCount : PrimIO Int

||| Safe wrapper: callback count
export
callbackCount : IO Int
callbackCount = primIO prim__callbackCount

--------------------------------------------------------------------------------
-- Error Code Descriptions
--------------------------------------------------------------------------------

||| Human-readable descriptions for overlay error codes
public export
overlayErrorDescription : Int -> String
overlayErrorDescription 0    = "Success"
overlayErrorDescription (-100) = "Not connected: overlay network not connected"
overlayErrorDescription (-101) = "Connection refused: daemon rejected connection"
overlayErrorDescription (-102) = "Timeout: operation timed out"
overlayErrorDescription (-103) = "Invalid argument: parameter was null or out of range"
overlayErrorDescription (-104) = "Not found: requested resource not found"
overlayErrorDescription (-105) = "Buffer too small: output buffer insufficient"
overlayErrorDescription (-106) = "Daemon not running: overlay daemon not available"
overlayErrorDescription (-107) = "Authentication failed: control port auth rejected"
overlayErrorDescription (-108) = "Not implemented: feature not yet available"
overlayErrorDescription (-199) = "Unknown overlay error"
overlayErrorDescription n    = "Unrecognised error code: " ++ show n
