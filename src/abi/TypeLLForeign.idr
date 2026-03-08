-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- ECHIDNA TypeLL Client ABI Foreign Function Declarations
--
-- Declares all C-compatible functions exported by the TypeLL client FFI layer
-- (ffi/zig/src/typell.zig) for type checking and type-level computation.
--
-- NO believe_me anywhere. All safety is enforced by types.

module TypeLL.Foreign

%default total

--------------------------------------------------------------------------------
-- Result types
--------------------------------------------------------------------------------

public export
data TypeLLResult : Type where
  TypeLLOk     : TypeLLResult
  TypeLLFailed : (code : Int) -> TypeLLResult

public export
typellResult : Int -> TypeLLResult
typellResult 0 = TypeLLOk
typellResult n = TypeLLFailed n

||| Type checking result (matches Zig CheckResult enum).
public export
data CheckResultKind = WellTyped | TypeMismatch | UnboundVariable | UniverseInconsistency | OccursCheckFailed | Ambiguous

public export
checkResultFromInt : Int -> CheckResultKind
checkResultFromInt 0 = WellTyped
checkResultFromInt 1 = TypeMismatch
checkResultFromInt 2 = UnboundVariable
checkResultFromInt 3 = UniverseInconsistency
checkResultFromInt 4 = OccursCheckFailed
checkResultFromInt _ = Ambiguous

||| Type universe levels.
public export
data UniverseLevel = Type0 | Type1 | Type2 | TypeOmega

public export
universeFromInt : Int -> UniverseLevel
universeFromInt 0 = Type0
universeFromInt 1 = Type1
universeFromInt 2 = Type2
universeFromInt _ = TypeOmega

||| TypeLL connection status.
public export
data TypeLLConnectionStatus = TypeLLDisconnected | TypeLLConnecting | TypeLLConnected | TypeLLError String

public export
typellStatusFromInt : Int -> TypeLLConnectionStatus
typellStatusFromInt 0 = TypeLLDisconnected
typellStatusFromInt 1 = TypeLLConnecting
typellStatusFromInt 2 = TypeLLConnected
typellStatusFromInt _ = TypeLLError "unknown"

||| String helper
export
%foreign "support:idris2_getString, libidris2_support"
prim__getString : Bits64 -> String

--------------------------------------------------------------------------------
-- Connection Functions
--------------------------------------------------------------------------------

export
%foreign "C:echidna_typell_connect, libechidna_typell"
prim__typellConnect : Bits64 -> Bits64 -> PrimIO Int

export
typellConnect : (configPtr : Bits64) -> (configLen : Bits64) -> IO TypeLLResult
typellConnect ptr len = do
  rc <- primIO (prim__typellConnect ptr len)
  pure (typellResult rc)

export
%foreign "C:echidna_typell_disconnect, libechidna_typell"
prim__typellDisconnect : PrimIO ()

export
typellDisconnect : IO ()
typellDisconnect = primIO prim__typellDisconnect

export
%foreign "C:echidna_typell_status, libechidna_typell"
prim__typellStatus : PrimIO Int

export
typellStatus : IO TypeLLConnectionStatus
typellStatus = do
  code <- primIO prim__typellStatus
  pure (typellStatusFromInt code)

export
%foreign "C:echidna_typell_health, libechidna_typell"
prim__typellHealth : Bits64 -> Bits64 -> PrimIO Int

export
typellHealth : (outPtr : Bits64) -> (outLenPtr : Bits64) -> IO TypeLLResult
typellHealth outPtr outLen = do
  rc <- primIO (prim__typellHealth outPtr outLen)
  pure (typellResult rc)

--------------------------------------------------------------------------------
-- Type Operations
--------------------------------------------------------------------------------

||| Type-check an expression.
export
%foreign "C:echidna_typell_check, libechidna_typell"
prim__typellCheck : Bits64 -> Bits64 -> Bits64 -> Bits64 -> Bits64 -> Bits64 -> PrimIO Int

export
typellCheck : (exprPtr : Bits64) -> (exprLen : Bits64) -> (ctxPtr : Bits64) -> (ctxLen : Bits64) -> (outPtr : Bits64) -> (outLenPtr : Bits64) -> IO TypeLLResult
typellCheck eP eL cP cL oP oL = do
  rc <- primIO (prim__typellCheck eP eL cP cL oP oL)
  pure (typellResult rc)

||| Infer the type of an expression.
export
%foreign "C:echidna_typell_infer, libechidna_typell"
prim__typellInfer : Bits64 -> Bits64 -> Bits64 -> Bits64 -> PrimIO Int

export
typellInfer : (exprPtr : Bits64) -> (exprLen : Bits64) -> (outPtr : Bits64) -> (outLenPtr : Bits64) -> IO TypeLLResult
typellInfer eP eL oP oL = do
  rc <- primIO (prim__typellInfer eP eL oP oL)
  pure (typellResult rc)

||| Apply refinement types.
export
%foreign "C:echidna_typell_refine, libechidna_typell"
prim__typellRefine : Bits64 -> Bits64 -> Bits64 -> Bits64 -> Bits64 -> Bits64 -> PrimIO Int

export
typellRefine : (specPtr : Bits64) -> (specLen : Bits64) -> (consPtr : Bits64) -> (consLen : Bits64) -> (outPtr : Bits64) -> (outLenPtr : Bits64) -> IO TypeLLResult
typellRefine sP sL cP cL oP oL = do
  rc <- primIO (prim__typellRefine sP sL cP cL oP oL)
  pure (typellResult rc)

||| Evaluate a type-level computation.
export
%foreign "C:echidna_typell_compute, libechidna_typell"
prim__typellCompute : Bits64 -> Bits64 -> Bits64 -> Bits64 -> PrimIO Int

export
typellCompute : (termPtr : Bits64) -> (termLen : Bits64) -> (outPtr : Bits64) -> (outLenPtr : Bits64) -> IO TypeLLResult
typellCompute tP tL oP oL = do
  rc <- primIO (prim__typellCompute tP tL oP oL)
  pure (typellResult rc)

||| List available type signatures.
export
%foreign "C:echidna_typell_list_signatures, libechidna_typell"
prim__typellListSignatures : Bits64 -> Bits64 -> PrimIO Int

export
typellListSignatures : (outPtr : Bits64) -> (outLenPtr : Bits64) -> IO TypeLLResult
typellListSignatures oP oL = do
  rc <- primIO (prim__typellListSignatures oP oL)
  pure (typellResult rc)

||| Get type universe hierarchy.
export
%foreign "C:echidna_typell_universes, libechidna_typell"
prim__typellUniverses : Bits64 -> Bits64 -> PrimIO Int

export
typellUniverses : (outPtr : Bits64) -> (outLenPtr : Bits64) -> IO TypeLLResult
typellUniverses oP oL = do
  rc <- primIO (prim__typellUniverses oP oL)
  pure (typellResult rc)

--------------------------------------------------------------------------------
-- Unified
--------------------------------------------------------------------------------

export
%foreign "C:echidna_typell_version, libechidna_typell"
prim__typellVersion : PrimIO Bits64

export
typellVersion : IO String
typellVersion = do
  ptr <- primIO prim__typellVersion
  pure (if ptr == 0 then "unknown" else prim__getString ptr)

export
%foreign "C:echidna_typell_last_error, libechidna_typell"
prim__typellLastError : PrimIO Bits64

export
typellLastError : IO (Maybe String)
typellLastError = do
  ptr <- primIO prim__typellLastError
  pure (if ptr == 0 then Nothing else Just (prim__getString ptr))

--------------------------------------------------------------------------------
-- Callback Registration
--------------------------------------------------------------------------------

export
%foreign "C:echidna_typell_register_on_status_change, libechidna_typell"
prim__typellRegisterOnStatusChange : Bits64 -> PrimIO Int

export
registerTypeLLOnStatusChange : (callbackPtr : Bits64) -> IO TypeLLResult
registerTypeLLOnStatusChange ptr = do
  rc <- primIO (prim__typellRegisterOnStatusChange ptr)
  pure (typellResult rc)

export
%foreign "C:echidna_typell_register_on_check_complete, libechidna_typell"
prim__typellRegisterOnCheckComplete : Bits64 -> PrimIO Int

export
registerTypeLLOnCheckComplete : (callbackPtr : Bits64) -> IO TypeLLResult
registerTypeLLOnCheckComplete ptr = do
  rc <- primIO (prim__typellRegisterOnCheckComplete ptr)
  pure (typellResult rc)

export
%foreign "C:echidna_typell_unregister_all_callbacks, libechidna_typell"
prim__typellUnregisterAllCallbacks : PrimIO Int

export
typellUnregisterAllCallbacks : IO TypeLLResult
typellUnregisterAllCallbacks = do
  rc <- primIO prim__typellUnregisterAllCallbacks
  pure (typellResult rc)

export
%foreign "C:echidna_typell_callback_count, libechidna_typell"
prim__typellCallbackCount : PrimIO Int

export
typellCallbackCount : IO Int
typellCallbackCount = primIO prim__typellCallbackCount

--------------------------------------------------------------------------------
-- Error Code Descriptions
--------------------------------------------------------------------------------

public export
typellErrorDescription : Int -> String
typellErrorDescription 0      = "Success"
typellErrorDescription (-300) = "Not connected: TypeLL server not connected"
typellErrorDescription (-301) = "Type error: expression does not type-check"
typellErrorDescription (-302) = "Parse error: invalid expression syntax"
typellErrorDescription (-303) = "Invalid argument"
typellErrorDescription (-304) = "Buffer too small"
typellErrorDescription (-305) = "Timeout"
typellErrorDescription (-306) = "Not implemented"
typellErrorDescription (-399) = "Unknown TypeLL error"
typellErrorDescription n      = "Unrecognised error code: " ++ show n
