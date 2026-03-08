-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- ECHIDNA BoJ Client ABI Foreign Function Declarations
--
-- Declares all C-compatible functions exported by the BoJ client FFI layer
-- (ffi/zig/src/boj.zig) for cartridge management and service discovery.
--
-- NO believe_me anywhere. All safety is enforced by types.

module Boj.Foreign

%default total

--------------------------------------------------------------------------------
-- Result types
--------------------------------------------------------------------------------

||| Convert a C int return code to success/failure.
public export
data BojResult : Type where
  BojOk     : BojResult
  BojFailed : (code : Int) -> BojResult

public export
bojResult : Int -> BojResult
bojResult 0 = BojOk
bojResult n = BojFailed n

||| Cartridge lifecycle status (matches Zig enum).
public export
data CartridgeStatus = Development | Ready | Deprecated | Faulty

public export
cartridgeStatusFromInt : Int -> CartridgeStatus
cartridgeStatusFromInt 0 = Development
cartridgeStatusFromInt 1 = Ready
cartridgeStatusFromInt 2 = Deprecated
cartridgeStatusFromInt _ = Faulty

||| BoJ connection status.
public export
data BojConnectionStatus = BojDisconnected | BojConnecting | BojConnected | BojError String

public export
bojStatusFromInt : Int -> BojConnectionStatus
bojStatusFromInt 0 = BojDisconnected
bojStatusFromInt 1 = BojConnecting
bojStatusFromInt 2 = BojConnected
bojStatusFromInt _ = BojError "unknown"

||| String helper
export
%foreign "support:idris2_getString, libidris2_support"
prim__getString : Bits64 -> String

--------------------------------------------------------------------------------
-- Connection Functions
--------------------------------------------------------------------------------

export
%foreign "C:echidna_boj_connect, libechidna_boj"
prim__bojConnect : Bits64 -> Bits64 -> PrimIO Int

export
bojConnect : (configPtr : Bits64) -> (configLen : Bits64) -> IO BojResult
bojConnect ptr len = do
  rc <- primIO (prim__bojConnect ptr len)
  pure (bojResult rc)

export
%foreign "C:echidna_boj_disconnect, libechidna_boj"
prim__bojDisconnect : PrimIO ()

export
bojDisconnect : IO ()
bojDisconnect = primIO prim__bojDisconnect

export
%foreign "C:echidna_boj_status, libechidna_boj"
prim__bojStatus : PrimIO Int

export
bojStatus : IO BojConnectionStatus
bojStatus = do
  code <- primIO prim__bojStatus
  pure (bojStatusFromInt code)

--------------------------------------------------------------------------------
-- Health and Discovery
--------------------------------------------------------------------------------

export
%foreign "C:echidna_boj_health, libechidna_boj"
prim__bojHealth : Bits64 -> Bits64 -> PrimIO Int

export
bojHealth : (outPtr : Bits64) -> (outLenPtr : Bits64) -> IO BojResult
bojHealth outPtr outLen = do
  rc <- primIO (prim__bojHealth outPtr outLen)
  pure (bojResult rc)

export
%foreign "C:echidna_boj_list_cartridges, libechidna_boj"
prim__bojListCartridges : Bits64 -> Bits64 -> PrimIO Int

export
bojListCartridges : (outPtr : Bits64) -> (outLenPtr : Bits64) -> IO BojResult
bojListCartridges outPtr outLen = do
  rc <- primIO (prim__bojListCartridges outPtr outLen)
  pure (bojResult rc)

export
%foreign "C:echidna_boj_get_cartridge, libechidna_boj"
prim__bojGetCartridge : Bits64 -> Bits64 -> Bits64 -> Bits64 -> PrimIO Int

export
bojGetCartridge : (namePtr : Bits64) -> (nameLen : Bits64) -> (outPtr : Bits64) -> (outLenPtr : Bits64) -> IO BojResult
bojGetCartridge nPtr nLen outPtr outLen = do
  rc <- primIO (prim__bojGetCartridge nPtr nLen outPtr outLen)
  pure (bojResult rc)

--------------------------------------------------------------------------------
-- Cartridge Management
--------------------------------------------------------------------------------

export
%foreign "C:echidna_boj_load_cartridge, libechidna_boj"
prim__bojLoadCartridge : Bits64 -> Bits64 -> PrimIO Int

export
bojLoadCartridge : (namePtr : Bits64) -> (nameLen : Bits64) -> IO BojResult
bojLoadCartridge ptr len = do
  rc <- primIO (prim__bojLoadCartridge ptr len)
  pure (bojResult rc)

export
%foreign "C:echidna_boj_unload_cartridge, libechidna_boj"
prim__bojUnloadCartridge : Bits64 -> Bits64 -> PrimIO Int

export
bojUnloadCartridge : (namePtr : Bits64) -> (nameLen : Bits64) -> IO BojResult
bojUnloadCartridge ptr len = do
  rc <- primIO (prim__bojUnloadCartridge ptr len)
  pure (bojResult rc)

export
%foreign "C:echidna_boj_invoke, libechidna_boj"
prim__bojInvoke : Bits64 -> Bits64 -> Bits64 -> Bits64 -> Bits64 -> Bits64 -> Bits64 -> Bits64 -> PrimIO Int

export
bojInvoke : (namePtr : Bits64) -> (nameLen : Bits64) -> (toolPtr : Bits64) -> (toolLen : Bits64) -> (argsPtr : Bits64) -> (argsLen : Bits64) -> (outPtr : Bits64) -> (outLenPtr : Bits64) -> IO BojResult
bojInvoke nP nL tP tL aP aL oP oL = do
  rc <- primIO (prim__bojInvoke nP nL tP tL aP aL oP oL)
  pure (bojResult rc)

--------------------------------------------------------------------------------
-- Topology and Federation
--------------------------------------------------------------------------------

export
%foreign "C:echidna_boj_topology, libechidna_boj"
prim__bojTopology : Bits64 -> Bits64 -> PrimIO Int

export
bojTopology : (outPtr : Bits64) -> (outLenPtr : Bits64) -> IO BojResult
bojTopology outPtr outLen = do
  rc <- primIO (prim__bojTopology outPtr outLen)
  pure (bojResult rc)

export
%foreign "C:echidna_boj_umoja_status, libechidna_boj"
prim__bojUmojaStatus : Bits64 -> Bits64 -> PrimIO Int

export
bojUmojaStatus : (outPtr : Bits64) -> (outLenPtr : Bits64) -> IO BojResult
bojUmojaStatus outPtr outLen = do
  rc <- primIO (prim__bojUmojaStatus outPtr outLen)
  pure (bojResult rc)

--------------------------------------------------------------------------------
-- Unified
--------------------------------------------------------------------------------

export
%foreign "C:echidna_boj_version, libechidna_boj"
prim__bojVersion : PrimIO Bits64

export
bojVersion : IO String
bojVersion = do
  ptr <- primIO prim__bojVersion
  pure (if ptr == 0 then "unknown" else prim__getString ptr)

export
%foreign "C:echidna_boj_last_error, libechidna_boj"
prim__bojLastError : PrimIO Bits64

export
bojLastError : IO (Maybe String)
bojLastError = do
  ptr <- primIO prim__bojLastError
  pure (if ptr == 0 then Nothing else Just (prim__getString ptr))

export
%foreign "C:echidna_boj_cartridge_count, libechidna_boj"
prim__bojCartridgeCount : PrimIO Int

export
bojCartridgeCount : IO Int
bojCartridgeCount = primIO prim__bojCartridgeCount

--------------------------------------------------------------------------------
-- Callback Registration
--------------------------------------------------------------------------------

export
%foreign "C:echidna_boj_register_on_status_change, libechidna_boj"
prim__bojRegisterOnStatusChange : Bits64 -> PrimIO Int

export
registerBojOnStatusChange : (callbackPtr : Bits64) -> IO BojResult
registerBojOnStatusChange ptr = do
  rc <- primIO (prim__bojRegisterOnStatusChange ptr)
  pure (bojResult rc)

export
%foreign "C:echidna_boj_register_on_cartridge_change, libechidna_boj"
prim__bojRegisterOnCartridgeChange : Bits64 -> PrimIO Int

export
registerBojOnCartridgeChange : (callbackPtr : Bits64) -> IO BojResult
registerBojOnCartridgeChange ptr = do
  rc <- primIO (prim__bojRegisterOnCartridgeChange ptr)
  pure (bojResult rc)

export
%foreign "C:echidna_boj_unregister_all_callbacks, libechidna_boj"
prim__bojUnregisterAllCallbacks : PrimIO Int

export
bojUnregisterAllCallbacks : IO BojResult
bojUnregisterAllCallbacks = do
  rc <- primIO prim__bojUnregisterAllCallbacks
  pure (bojResult rc)

export
%foreign "C:echidna_boj_callback_count, libechidna_boj"
prim__bojCallbackCount : PrimIO Int

export
bojCallbackCount : IO Int
bojCallbackCount = primIO prim__bojCallbackCount

--------------------------------------------------------------------------------
-- Error Code Descriptions
--------------------------------------------------------------------------------

public export
bojErrorDescription : Int -> String
bojErrorDescription 0      = "Success"
bojErrorDescription (-200) = "Not connected: BoJ server not connected"
bojErrorDescription (-201) = "Server unavailable: BoJ server not reachable"
bojErrorDescription (-202) = "Cartridge not found"
bojErrorDescription (-203) = "Cartridge not ready: status is not Ready"
bojErrorDescription (-204) = "Invoke failed: cartridge tool invocation error"
bojErrorDescription (-205) = "Invalid argument"
bojErrorDescription (-206) = "Buffer too small"
bojErrorDescription (-207) = "Timeout"
bojErrorDescription (-299) = "Unknown BoJ error"
bojErrorDescription n      = "Unrecognised error code: " ++ show n
