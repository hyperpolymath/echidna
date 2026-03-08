-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| ECHIDNA ABI Foreign Function Declarations
|||
||| Declares all C-compatible functions exported by the Rust FFI layer
||| (src/rust/ffi/mod.rs) and consumed by the Zig FFI bridge (ffi/zig/).
|||
||| Every FFI function has:
|||   1. A raw PrimIO declaration matching the C symbol
|||   2. A safe Idris2 wrapper with proper error handling
|||
||| NO believe_me anywhere. All safety is enforced by types.

module EchidnaABI.Foreign

import EchidnaABI.Types
import EchidnaABI.Layout

%default total

--------------------------------------------------------------------------------
-- Library Lifecycle
--------------------------------------------------------------------------------

||| Initialise the ECHIDNA library.
||| C signature: int32_t echidna_init(void);
||| Returns FfiOk (0) on success, negative error code on failure.
export
%foreign "C:echidna_init, libechidna"
prim__init : PrimIO Int32

||| Safe wrapper for library initialisation
export
echidnaInit : IO FfiStatus
echidnaInit = do
  code <- primIO prim__init
  pure $ case ffiStatusFromI32 code of
    Just s  => s
    Nothing => FfiErrorUnknown

||| Free all ECHIDNA library resources.
||| C signature: void echidna_free(void);
export
%foreign "C:echidna_free, libechidna"
prim__free : PrimIO ()

||| Safe wrapper for library shutdown
export
echidnaFree : IO ()
echidnaFree = primIO prim__free

--------------------------------------------------------------------------------
-- Prover Registry
--------------------------------------------------------------------------------

||| Create a prover backend instance and return an opaque handle.
||| C signature: uint64_t echidna_create_prover(uint8_t kind);
||| Returns 0 on failure (null handle), non-zero on success.
export
%foreign "C:echidna_create_prover, libechidna"
prim__createProver : Bits8 -> PrimIO Bits64

||| Safe wrapper: create a prover, returning a non-null Handle on success
export
echidnaCreateProver : ProverKind -> IO (Maybe Handle)
echidnaCreateProver kind = do
  ptr <- primIO (prim__createProver (proverKindToU8 kind))
  pure (createHandle ptr)

||| Destroy a prover backend instance.
||| C signature: void echidna_destroy_prover(uint64_t handle);
export
%foreign "C:echidna_destroy_prover, libechidna"
prim__destroyProver : Bits64 -> PrimIO ()

||| Safe wrapper: destroy a prover by handle.
||| The Handle's non-null proof guarantees we never pass 0.
export
echidnaDestroyProver : Handle -> IO ()
echidnaDestroyProver h = primIO (prim__destroyProver (handlePtr h))

--------------------------------------------------------------------------------
-- Proof Parsing
--------------------------------------------------------------------------------

||| Parse a proof file through a specific prover backend.
||| C signature: int32_t rust_parse_file(uint8_t kind, FfiStringSlice path, void** out_state);
||| On success, out_state is set to a valid ProofState pointer.
export
%foreign "C:rust_parse_file, libechidna"
prim__parseFile : Bits8 -> Bits64 -> Bits64 -> Bits64 -> PrimIO Int32

||| Safe wrapper for parsing a proof file.
||| Takes a ProverKind and file path; returns FfiStatus.
||| The caller is responsible for managing the returned state handle.
export
echidnaParseFile : ProverKind -> (pathPtr : Bits64) -> (pathLen : Bits64) -> (outState : Bits64) -> IO FfiStatus
echidnaParseFile kind pathPtr pathLen outState = do
  code <- primIO (prim__parseFile (proverKindToU8 kind) pathPtr pathLen outState)
  pure $ case ffiStatusFromI32 code of
    Just s  => s
    Nothing => FfiErrorUnknown

||| Parse a proof from a string buffer.
||| C signature: int32_t rust_parse_string(uint8_t kind, FfiStringSlice content, void** out_state);
export
%foreign "C:rust_parse_string, libechidna"
prim__parseString : Bits8 -> Bits64 -> Bits64 -> Bits64 -> PrimIO Int32

||| Safe wrapper for parsing a proof from string content
export
echidnaParseString : ProverKind -> (contentPtr : Bits64) -> (contentLen : Bits64) -> (outState : Bits64) -> IO FfiStatus
echidnaParseString kind contentPtr contentLen outState = do
  code <- primIO (prim__parseString (proverKindToU8 kind) contentPtr contentLen outState)
  pure $ case ffiStatusFromI32 code of
    Just s  => s
    Nothing => FfiErrorUnknown

--------------------------------------------------------------------------------
-- Tactic Application
--------------------------------------------------------------------------------

||| Apply a tactic to the current proof state.
||| C signature: int32_t rust_apply_tactic(uint8_t kind, void* state, const FfiTactic* tactic, FfiTacticResult* out_result);
export
%foreign "C:rust_apply_tactic, libechidna"
prim__applyTactic : Bits8 -> Bits64 -> Bits64 -> Bits64 -> PrimIO Int32

||| Safe wrapper for tactic application.
||| Requires a valid Handle (non-null proof state).
export
echidnaApplyTactic : ProverKind -> Handle -> (tacticPtr : Bits64) -> (outResultPtr : Bits64) -> IO FfiStatus
echidnaApplyTactic kind stateHandle tacticPtr outResultPtr = do
  code <- primIO (prim__applyTactic (proverKindToU8 kind) (handlePtr stateHandle) tacticPtr outResultPtr)
  pure $ case ffiStatusFromI32 code of
    Just s  => s
    Nothing => FfiErrorUnknown

--------------------------------------------------------------------------------
-- Proof Verification
--------------------------------------------------------------------------------

||| Verify a proof in the current state.
||| C signature: int32_t rust_verify_proof(uint8_t kind, void* state, bool* out_valid);
export
%foreign "C:rust_verify_proof, libechidna"
prim__verifyProof : Bits8 -> Bits64 -> Bits64 -> PrimIO Int32

||| Safe wrapper for proof verification
export
echidnaVerifyProof : ProverKind -> Handle -> (outValidPtr : Bits64) -> IO FfiStatus
echidnaVerifyProof kind stateHandle outValidPtr = do
  code <- primIO (prim__verifyProof (proverKindToU8 kind) (handlePtr stateHandle) outValidPtr)
  pure $ case ffiStatusFromI32 code of
    Just s  => s
    Nothing => FfiErrorUnknown

--------------------------------------------------------------------------------
-- Proof Export
--------------------------------------------------------------------------------

||| Export a proof to the prover's native format.
||| C signature: int32_t rust_export_proof(uint8_t kind, void* state, FfiOwnedString* out_content);
export
%foreign "C:rust_export_proof, libechidna"
prim__exportProof : Bits8 -> Bits64 -> Bits64 -> PrimIO Int32

||| Safe wrapper for proof export
export
echidnaExportProof : ProverKind -> Handle -> (outContentPtr : Bits64) -> IO FfiStatus
echidnaExportProof kind stateHandle outContentPtr = do
  code <- primIO (prim__exportProof (proverKindToU8 kind) (handlePtr stateHandle) outContentPtr)
  pure $ case ffiStatusFromI32 code of
    Just s  => s
    Nothing => FfiErrorUnknown

--------------------------------------------------------------------------------
-- Tactic Suggestion (Neural Premise Selection)
--------------------------------------------------------------------------------

||| Suggest tactics using neural premise selection.
||| C signature: int32_t rust_suggest_tactics(uint8_t kind, void* state, uint32_t limit, FfiTactic* out_tactics, uint32_t* out_count);
export
%foreign "C:rust_suggest_tactics, libechidna"
prim__suggestTactics : Bits8 -> Bits64 -> Bits32 -> Bits64 -> Bits64 -> PrimIO Int32

||| Safe wrapper for tactic suggestion
export
echidnaSuggestTactics : ProverKind -> Handle -> (limit : Bits32) -> (outTacticsPtr : Bits64) -> (outCountPtr : Bits64) -> IO FfiStatus
echidnaSuggestTactics kind stateHandle limit outTacticsPtr outCountPtr = do
  code <- primIO (prim__suggestTactics (proverKindToU8 kind) (handlePtr stateHandle) limit outTacticsPtr outCountPtr)
  pure $ case ffiStatusFromI32 code of
    Just s  => s
    Nothing => FfiErrorUnknown

--------------------------------------------------------------------------------
-- Trust-Hardening Dispatch Pipeline
--------------------------------------------------------------------------------

||| Dispatch a proof through the full trust-hardening pipeline.
||| C signature: int32_t echidna_dispatch_verify(const DispatchConfig* config, FfiStringSlice proof_content);
||| Pipeline: integrity check -> sandbox -> prove -> certificate -> axiom scan -> confidence
export
%foreign "C:echidna_dispatch_verify, libechidna"
prim__dispatchVerify : Bits64 -> Bits64 -> Bits64 -> PrimIO Int32

||| Safe wrapper for the dispatch pipeline.
||| Takes a pointer to DispatchConfig and the proof content as a string slice.
export
echidnaDispatchVerify : (configPtr : Bits64) -> (proofPtr : Bits64) -> (proofLen : Bits64) -> IO FfiStatus
echidnaDispatchVerify configPtr proofPtr proofLen = do
  code <- primIO (prim__dispatchVerify configPtr proofPtr proofLen)
  pure $ case ffiStatusFromI32 code of
    Just s  => s
    Nothing => FfiErrorUnknown

||| Dispatch a proof with cross-checking (portfolio solving).
||| C signature: int32_t echidna_dispatch_cross_check(const DispatchConfig* config, FfiStringSlice proof_content, const uint8_t* prover_kinds, uint32_t prover_count);
export
%foreign "C:echidna_dispatch_cross_check, libechidna"
prim__dispatchCrossCheck : Bits64 -> Bits64 -> Bits64 -> Bits64 -> Bits32 -> PrimIO Int32

||| Safe wrapper for cross-checked dispatch
export
echidnaDispatchCrossCheck :
  (configPtr : Bits64) ->
  (proofPtr : Bits64) ->
  (proofLen : Bits64) ->
  (proverKindsPtr : Bits64) ->
  (proverCount : Bits32) ->
  IO FfiStatus
echidnaDispatchCrossCheck configPtr proofPtr proofLen kindsPtr count = do
  code <- primIO (prim__dispatchCrossCheck configPtr proofPtr proofLen kindsPtr count)
  pure $ case ffiStatusFromI32 code of
    Just s  => s
    Nothing => FfiErrorUnknown

--------------------------------------------------------------------------------
-- Version and Information Queries
--------------------------------------------------------------------------------

||| Get the ECHIDNA library version string.
||| C signature: const char* echidna_version(void);
||| Returns a pointer to a static null-terminated string.
export
%foreign "C:echidna_version, libechidna"
prim__version : PrimIO Bits64

||| Get the library version as an Idris String
export
%foreign "support:idris2_getString, libidris2_support"
prim__getString : Bits64 -> String

||| Safe wrapper for version query
export
echidnaVersion : IO String
echidnaVersion = do
  ptr <- primIO prim__version
  pure (if ptr == 0 then "unknown" else prim__getString ptr)

||| Get the library build info string.
||| C signature: const char* echidna_build_info(void);
export
%foreign "C:echidna_build_info, libechidna"
prim__buildInfo : PrimIO Bits64

||| Safe wrapper for build info query
export
echidnaBuildInfo : IO String
echidnaBuildInfo = do
  ptr <- primIO prim__buildInfo
  pure (if ptr == 0 then "unknown" else prim__getString ptr)

||| Get the number of supported provers.
||| C signature: uint32_t echidna_prover_count(void);
export
%foreign "C:echidna_prover_count, libechidna"
prim__proverCount : PrimIO Bits32

||| Safe wrapper: number of supported provers (should be 30)
export
echidnaProverCount : IO Bits32
echidnaProverCount = primIO prim__proverCount

||| Check whether a specific prover is available on this system.
||| C signature: bool echidna_prover_available(uint8_t kind);
export
%foreign "C:echidna_prover_available, libechidna"
prim__proverAvailable : Bits8 -> PrimIO Bits8

||| Safe wrapper: check prover availability
export
echidnaProverAvailable : ProverKind -> IO Bool
echidnaProverAvailable kind = do
  result <- primIO (prim__proverAvailable (proverKindToU8 kind))
  pure (result /= 0)

--------------------------------------------------------------------------------
-- Error Reporting
--------------------------------------------------------------------------------

||| Get the last error message.
||| C signature: const char* echidna_last_error(void);
||| Returns a pointer to a thread-local static string, or null if no error.
export
%foreign "C:echidna_last_error, libechidna"
prim__lastError : PrimIO Bits64

||| Safe wrapper: retrieve last error message, if any
export
echidnaLastError : IO (Maybe String)
echidnaLastError = do
  ptr <- primIO prim__lastError
  pure (if ptr == 0 then Nothing else Just (prim__getString ptr))

||| Get a human-readable description for an FfiStatus code
export
ffiStatusDescription : FfiStatus -> String
ffiStatusDescription FfiOk                       = "Success"
ffiStatusDescription FfiErrorInvalidHandle       = "Invalid handle: the handle does not refer to a live prover"
ffiStatusDescription FfiErrorInvalidArgument     = "Invalid argument: a parameter was null or out of range"
ffiStatusDescription FfiErrorProverNotFound      = "Prover not found: the requested prover backend is not available"
ffiStatusDescription FfiErrorParseFailure        = "Parse failure: the proof content could not be parsed"
ffiStatusDescription FfiErrorTacticFailure       = "Tactic failure: the tactic could not be applied to the current state"
ffiStatusDescription FfiErrorVerificationFailure = "Verification failure: the proof did not verify"
ffiStatusDescription FfiErrorOutOfMemory         = "Out of memory"
ffiStatusDescription FfiErrorTimeout             = "Timeout: the prover exceeded its time limit"
ffiStatusDescription FfiErrorNotImplemented      = "Not implemented: this operation is not yet supported"
ffiStatusDescription FfiErrorNotInitialized      = "Not initialised: call echidna_init() first"
ffiStatusDescription FfiErrorUnknown             = "Unknown error"

--------------------------------------------------------------------------------
-- Memory Management Helpers
--------------------------------------------------------------------------------

||| Free an FfiOwnedString that was returned by a previous FFI call.
||| C signature: void echidna_free_string(FfiOwnedString* str);
export
%foreign "C:echidna_free_string, libechidna"
prim__freeString : Bits64 -> PrimIO ()

||| Safe wrapper for freeing an owned string
export
echidnaFreeString : (ownedStringPtr : Bits64) -> IO ()
echidnaFreeString ptr = primIO (prim__freeString ptr)

||| Free a proof state that was returned by parsing.
||| C signature: void echidna_free_state(void* state);
export
%foreign "C:echidna_free_state, libechidna"
prim__freeState : Bits64 -> PrimIO ()

||| Safe wrapper for freeing a proof state.
||| Consumes the Handle (caller should not use it after this call).
export
echidnaFreeState : Handle -> IO ()
echidnaFreeState h = primIO (prim__freeState (handlePtr h))

--------------------------------------------------------------------------------
-- Initialisation Check
--------------------------------------------------------------------------------

||| Check whether the library has been initialised.
||| C signature: bool echidna_is_initialized(void);
export
%foreign "C:echidna_is_initialized, libechidna"
prim__isInitialized : PrimIO Bits8

||| Safe wrapper for initialisation check
export
echidnaIsInitialized : IO Bool
echidnaIsInitialized = do
  result <- primIO prim__isInitialized
  pure (result /= 0)

--------------------------------------------------------------------------------
-- Callback Registration (Zig FFI layer — libechidna_ffi)
--------------------------------------------------------------------------------
--
-- These functions register callback function pointers with the Zig FFI
-- bridge. The Zig layer invokes these callbacks on state transitions,
-- prover events, and errors, enabling bidirectional ABI ↔ FFI communication.

||| Register a callback for FFI init/deinit state changes.
||| Callback signature: void(int old_state, int new_state)
||| Pass 0 to unregister.
export
%foreign "C:echidna_register_on_init_change, libechidna_ffi"
prim__registerOnInitChange : Bits64 -> PrimIO Int

export
registerOnInitChange : (callbackPtr : Bits64) -> IO Int
registerOnInitChange ptr = primIO (prim__registerOnInitChange ptr)

||| Register a callback for prover create/destroy events.
||| Callback signature: void(int handle_id, int prover_kind, int created)
||| Pass 0 to unregister.
export
%foreign "C:echidna_register_on_prover_change, libechidna_ffi"
prim__registerOnProverChange : Bits64 -> PrimIO Int

export
registerOnProverChange : (callbackPtr : Bits64) -> IO Int
registerOnProverChange ptr = primIO (prim__registerOnProverChange ptr)

||| Register a callback for FFI errors.
||| Callback signature: void(int error_code, const uint8_t* msg_ptr, size_t msg_len)
||| Pass 0 to unregister.
export
%foreign "C:echidna_register_on_error, libechidna_ffi"
prim__registerOnFfiError : Bits64 -> PrimIO Int

export
registerOnFfiError : (callbackPtr : Bits64) -> IO Int
registerOnFfiError ptr = primIO (prim__registerOnFfiError ptr)

||| Register a callback for verification completion.
||| Callback signature: void(int handle_id, int prover_kind, int verified)
||| Pass 0 to unregister.
export
%foreign "C:echidna_register_on_verify_complete, libechidna_ffi"
prim__registerOnVerifyComplete : Bits64 -> PrimIO Int

export
registerOnVerifyComplete : (callbackPtr : Bits64) -> IO Int
registerOnVerifyComplete ptr = primIO (prim__registerOnVerifyComplete ptr)

||| Unregister all FFI callbacks at once.
export
%foreign "C:echidna_unregister_all_callbacks, libechidna_ffi"
prim__unregisterAllCallbacks : PrimIO Int

export
unregisterAllCallbacks : IO Int
unregisterAllCallbacks = primIO prim__unregisterAllCallbacks

||| Get the number of currently registered FFI callbacks (0-4).
export
%foreign "C:echidna_callback_count, libechidna_ffi"
prim__callbackCount : PrimIO Int

export
callbackCount : IO Int
callbackCount = primIO prim__callbackCount
