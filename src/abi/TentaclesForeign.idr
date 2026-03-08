-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- ECHIDNA Tentacles ABI Foreign Function Declarations
--
-- Declares all C-compatible functions exported by the Tentacles FFI layer
-- (ffi/zig/src/tentacles.zig) for agent management, task dispatch, OODA
-- phase tracking, and event streaming.
--
-- The 7-Tentacles system maps compiler subsystems to colour-coded agents:
--   Red=Parser, Orange=Concurrency, Yellow=TypeSystem, Green=ASTArchitect,
--   Blue=Auditor, Indigo=Metaprogrammer, Violet=Governance
--
-- NO believe_me anywhere. All safety is enforced by types.

module Tentacles.Foreign

%default total

--------------------------------------------------------------------------------
-- Agent identifiers (matching Zig enum)
--------------------------------------------------------------------------------

||| Tentacle agent colour identifier.
public export
data TentacleId = Red | Orange | Yellow | Green | Blue | Indigo | Violet

public export
tentacleIdToInt : TentacleId -> Int
tentacleIdToInt Red    = 0
tentacleIdToInt Orange = 1
tentacleIdToInt Yellow = 2
tentacleIdToInt Green  = 3
tentacleIdToInt Blue   = 4
tentacleIdToInt Indigo = 5
tentacleIdToInt Violet = 6

public export
tentacleIdFromInt : Int -> Maybe TentacleId
tentacleIdFromInt 0 = Just Red
tentacleIdFromInt 1 = Just Orange
tentacleIdFromInt 2 = Just Yellow
tentacleIdFromInt 3 = Just Green
tentacleIdFromInt 4 = Just Blue
tentacleIdFromInt 5 = Just Indigo
tentacleIdFromInt 6 = Just Violet
tentacleIdFromInt _ = Nothing

||| OODA loop phase.
public export
data OodaPhase = Observe | Orient | Decide | Act

public export
oodaPhaseToInt : OodaPhase -> Int
oodaPhaseToInt Observe = 0
oodaPhaseToInt Orient  = 1
oodaPhaseToInt Decide  = 2
oodaPhaseToInt Act     = 3

public export
oodaPhaseFromInt : Int -> Maybe OodaPhase
oodaPhaseFromInt 0 = Just Observe
oodaPhaseFromInt 1 = Just Orient
oodaPhaseFromInt 2 = Just Decide
oodaPhaseFromInt 3 = Just Act
oodaPhaseFromInt _ = Nothing

||| Progressive reveal stage.
public export
data TentacleStage = Cuttle | Squidlet | Duet | Octopus

public export
stageToInt : TentacleStage -> Int
stageToInt Cuttle   = 0
stageToInt Squidlet = 1
stageToInt Duet     = 2
stageToInt Octopus  = 3

public export
stageFromInt : Int -> Maybe TentacleStage
stageFromInt 0 = Just Cuttle
stageFromInt 1 = Just Squidlet
stageFromInt 2 = Just Duet
stageFromInt 3 = Just Octopus
stageFromInt _ = Nothing

--------------------------------------------------------------------------------
-- Result types
--------------------------------------------------------------------------------

||| Convert a C int return code to success/failure.
public export
data TentaclesResult : Type where
  TentaclesOk     : TentaclesResult
  TentaclesFailed : (code : Int) -> TentaclesResult

public export
tentaclesResult : Int -> TentaclesResult
tentaclesResult 0 = TentaclesOk
tentaclesResult n = TentaclesFailed n

||| Agent status values.
public export
data AgentStatus = AgentIdle | AgentBusy | AgentError | AgentDisabled

public export
agentStatusFromInt : Int -> AgentStatus
agentStatusFromInt 0 = AgentIdle
agentStatusFromInt 1 = AgentBusy
agentStatusFromInt 2 = AgentError
agentStatusFromInt _ = AgentDisabled

||| String helper
export
%foreign "support:idris2_getString, libidris2_support"
prim__getString : Bits64 -> String

--------------------------------------------------------------------------------
-- Initialisation
--------------------------------------------------------------------------------

export
%foreign "C:echidna_tentacles_init, libechidna_tentacles"
prim__tentaclesInit : PrimIO Int

export
tentaclesInit : IO TentaclesResult
tentaclesInit = do
  rc <- primIO prim__tentaclesInit
  pure (tentaclesResult rc)

export
%foreign "C:echidna_tentacles_shutdown, libechidna_tentacles"
prim__tentaclesShutdown : PrimIO ()

export
tentaclesShutdown : IO ()
tentaclesShutdown = primIO prim__tentaclesShutdown

--------------------------------------------------------------------------------
-- Agent queries
--------------------------------------------------------------------------------

export
%foreign "C:echidna_tentacles_agent_status, libechidna_tentacles"
prim__agentStatus : Int -> PrimIO Int

export
agentStatus : TentacleId -> IO AgentStatus
agentStatus tid = do
  code <- primIO (prim__agentStatus (tentacleIdToInt tid))
  pure (agentStatusFromInt code)

export
%foreign "C:echidna_tentacles_agent_phase, libechidna_tentacles"
prim__agentPhase : Int -> PrimIO Int

export
agentPhase : TentacleId -> IO (Maybe OodaPhase)
agentPhase tid = do
  code <- primIO (prim__agentPhase (tentacleIdToInt tid))
  pure (oodaPhaseFromInt code)

export
%foreign "C:echidna_tentacles_agent_stage, libechidna_tentacles"
prim__agentStage : Int -> PrimIO Int

export
agentStage : TentacleId -> IO (Maybe TentacleStage)
agentStage tid = do
  code <- primIO (prim__agentStage (tentacleIdToInt tid))
  pure (stageFromInt code)

--------------------------------------------------------------------------------
-- Task dispatch
--------------------------------------------------------------------------------

export
%foreign "C:echidna_tentacles_dispatch_task, libechidna_tentacles"
prim__dispatchTask : Int -> Bits64 -> Bits64 -> PrimIO Int

export
dispatchTask : TentacleId -> (taskPtr : Bits64) -> (taskLen : Bits64) -> IO TentaclesResult
dispatchTask tid ptr len = do
  rc <- primIO (prim__dispatchTask (tentacleIdToInt tid) ptr len)
  pure (tentaclesResult rc)

export
%foreign "C:echidna_tentacles_cancel_task, libechidna_tentacles"
prim__cancelTask : Int -> PrimIO Int

export
cancelTask : TentacleId -> IO TentaclesResult
cancelTask tid = do
  rc <- primIO (prim__cancelTask (tentacleIdToInt tid))
  pure (tentaclesResult rc)

--------------------------------------------------------------------------------
-- Stage management
--------------------------------------------------------------------------------

export
%foreign "C:echidna_tentacles_set_global_stage, libechidna_tentacles"
prim__setGlobalStage : Int -> PrimIO Int

export
setGlobalStage : TentacleStage -> IO TentaclesResult
setGlobalStage stage = do
  rc <- primIO (prim__setGlobalStage (stageToInt stage))
  pure (tentaclesResult rc)

export
%foreign "C:echidna_tentacles_get_global_stage, libechidna_tentacles"
prim__getGlobalStage : PrimIO Int

export
getGlobalStage : IO (Maybe TentacleStage)
getGlobalStage = do
  code <- primIO prim__getGlobalStage
  pure (stageFromInt code)

--------------------------------------------------------------------------------
-- Event polling
--------------------------------------------------------------------------------

export
%foreign "C:echidna_tentacles_poll_events, libechidna_tentacles"
prim__pollEvents : Bits64 -> Bits64 -> PrimIO Int

export
pollEvents : (outPtr : Bits64) -> (outLenPtr : Bits64) -> IO TentaclesResult
pollEvents outPtr outLen = do
  rc <- primIO (prim__pollEvents outPtr outLen)
  pure (tentaclesResult rc)

export
%foreign "C:echidna_tentacles_event_count, libechidna_tentacles"
prim__eventCount : PrimIO Int

export
eventCount : IO Int
eventCount = primIO prim__eventCount

--------------------------------------------------------------------------------
-- Broadcast
--------------------------------------------------------------------------------

export
%foreign "C:echidna_tentacles_broadcast, libechidna_tentacles"
prim__broadcast : Int -> Bits64 -> Bits64 -> PrimIO Int

export
broadcast : TentacleId -> (payloadPtr : Bits64) -> (payloadLen : Bits64) -> IO TentaclesResult
broadcast tid ptr len = do
  rc <- primIO (prim__broadcast (tentacleIdToInt tid) ptr len)
  pure (tentaclesResult rc)

--------------------------------------------------------------------------------
-- Callback registration
--------------------------------------------------------------------------------

export
%foreign "C:echidna_tentacles_register_on_phase_change, libechidna_tentacles"
prim__registerOnPhaseChange : Bits64 -> PrimIO Int

export
registerOnPhaseChange : (callbackPtr : Bits64) -> IO TentaclesResult
registerOnPhaseChange ptr = do
  rc <- primIO (prim__registerOnPhaseChange ptr)
  pure (tentaclesResult rc)

export
%foreign "C:echidna_tentacles_register_on_task_complete, libechidna_tentacles"
prim__registerOnTaskComplete : Bits64 -> PrimIO Int

export
registerOnTaskComplete : (callbackPtr : Bits64) -> IO TentaclesResult
registerOnTaskComplete ptr = do
  rc <- primIO (prim__registerOnTaskComplete ptr)
  pure (tentaclesResult rc)

export
%foreign "C:echidna_tentacles_register_on_error, libechidna_tentacles"
prim__registerOnError : Bits64 -> PrimIO Int

export
registerOnError : (callbackPtr : Bits64) -> IO TentaclesResult
registerOnError ptr = do
  rc <- primIO (prim__registerOnError ptr)
  pure (tentaclesResult rc)

export
%foreign "C:echidna_tentacles_unregister_all_callbacks, libechidna_tentacles"
prim__unregisterAllCallbacks : PrimIO Int

export
unregisterAllCallbacks : IO TentaclesResult
unregisterAllCallbacks = do
  rc <- primIO prim__unregisterAllCallbacks
  pure (tentaclesResult rc)

--------------------------------------------------------------------------------
-- Unified
--------------------------------------------------------------------------------

export
%foreign "C:echidna_tentacles_version, libechidna_tentacles"
prim__tentaclesVersion : PrimIO Bits64

export
tentaclesVersion : IO String
tentaclesVersion = do
  ptr <- primIO prim__tentaclesVersion
  pure (if ptr == 0 then "unknown" else prim__getString ptr)

export
%foreign "C:echidna_tentacles_last_error, libechidna_tentacles"
prim__tentaclesLastError : PrimIO Bits64

export
tentaclesLastError : IO (Maybe String)
tentaclesLastError = do
  ptr <- primIO prim__tentaclesLastError
  pure (if ptr == 0 then Nothing else Just (prim__getString ptr))

export
%foreign "C:echidna_tentacles_agent_count, libechidna_tentacles"
prim__agentCount : PrimIO Int

export
agentCount : IO Int
agentCount = primIO prim__agentCount

--------------------------------------------------------------------------------
-- Error Code Descriptions
--------------------------------------------------------------------------------

public export
tentaclesErrorDescription : Int -> String
tentaclesErrorDescription 0      = "Success"
tentaclesErrorDescription (-300) = "Not initialised: tentacles system not started"
tentaclesErrorDescription (-301) = "Invalid agent: unknown tentacle ID"
tentaclesErrorDescription (-302) = "Agent busy: task already in progress"
tentaclesErrorDescription (-303) = "Agent error: agent in error state"
tentaclesErrorDescription (-304) = "Task failed: task execution error"
tentaclesErrorDescription (-305) = "Invalid stage: unknown stage value"
tentaclesErrorDescription (-306) = "Buffer too small"
tentaclesErrorDescription (-307) = "Broadcast failed"
tentaclesErrorDescription (-399) = "Unknown tentacles error"
tentaclesErrorDescription n      = "Unrecognised error code: " ++ show n
