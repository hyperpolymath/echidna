||| Foreign Function Interface Declarations
|||
||| This module declares all C-compatible functions that will be
||| implemented in the Zig FFI layer.
|||
||| All functions are declared here with type signatures and safety proofs.
||| Implementations live in ffi/zig/

module ECHIDNA.ABI.Foreign

import ECHIDNA.ABI.Types
import ECHIDNA.ABI.Layout

%default total

--------------------------------------------------------------------------------
-- Library Lifecycle
--------------------------------------------------------------------------------

||| Initialize the library
||| Returns a handle to the library instance, or Nothing on failure
export
%foreign "C:echidna_init, libechidna"
prim__init : PrimIO Bits64

||| Safe wrapper for library initialization
export
init : IO (Maybe Handle)
init = do
  ptr <- primIO prim__init
  pure (createHandle ptr)

||| Clean up library resources
export
%foreign "C:echidna_free, libechidna"
prim__free : Bits64 -> PrimIO ()

||| Safe wrapper for cleanup
export
free : Handle -> IO ()
free h = primIO (prim__free (handlePtr h))

--------------------------------------------------------------------------------
-- Core Operations
--------------------------------------------------------------------------------

||| Example operation: process data
export
%foreign "C:echidna_process, libechidna"
prim__process : Bits64 -> Bits32 -> PrimIO Bits32

||| Safe wrapper with error handling
export
process : Handle -> Bits32 -> IO (Either Result Bits32)
process h input = do
  result <- primIO (prim__process (handlePtr h) input)
  pure $ case result of
    0 => Left Error
    n => Right n

--------------------------------------------------------------------------------
-- String Operations
--------------------------------------------------------------------------------

||| Convert C string to Idris String
export
%foreign "support:idris2_getString, libidris2_support"
prim__getString : Bits64 -> String

||| Free C string
export
%foreign "C:echidna_free_string, libechidna"
prim__freeString : Bits64 -> PrimIO ()

||| Get string result from library
export
%foreign "C:echidna_get_string, libechidna"
prim__getResult : Bits64 -> PrimIO Bits64

||| Safe string getter
export
getString : Handle -> IO (Maybe String)
getString h = do
  ptr <- primIO (prim__getResult (handlePtr h))
  if ptr == 0
    then pure Nothing
    else do
      let str = prim__getString ptr
      primIO (prim__freeString ptr)
      pure (Just str)

--------------------------------------------------------------------------------
-- Array/Buffer Operations
--------------------------------------------------------------------------------

||| Process array data
export
%foreign "C:echidna_process_array, libechidna"
prim__processArray : Bits64 -> Bits64 -> Bits32 -> PrimIO Bits32

||| Safe array processor
export
processArray : Handle -> (buffer : Bits64) -> (len : Bits32) -> IO (Either Result ())
processArray h buf len = do
  result <- primIO (prim__processArray (handlePtr h) buf len)
  pure $ case resultFromInt result of
    Just Ok => Right ()
    Just err => Left err
    Nothing => Left Error
  where
    resultFromInt : Bits32 -> Maybe Result
    resultFromInt 0 = Just Ok
    resultFromInt 1 = Just Error
    resultFromInt 2 = Just InvalidParam
    resultFromInt 3 = Just OutOfMemory
    resultFromInt 4 = Just NullPointer
    resultFromInt _ = Nothing

--------------------------------------------------------------------------------
-- Error Handling
--------------------------------------------------------------------------------

||| Get last error message
export
%foreign "C:echidna_last_error, libechidna"
prim__lastError : PrimIO Bits64

||| Retrieve last error as string
export
lastError : IO (Maybe String)
lastError = do
  ptr <- primIO prim__lastError
  if ptr == 0
    then pure Nothing
    else pure (Just (prim__getString ptr))

||| Get error description for result code
export
errorDescription : Result -> String
errorDescription Ok = "Success"
errorDescription Error = "Generic error"
errorDescription InvalidParam = "Invalid parameter"
errorDescription OutOfMemory = "Out of memory"
errorDescription NullPointer = "Null pointer"

--------------------------------------------------------------------------------
-- Version Information
--------------------------------------------------------------------------------

||| Get library version
export
%foreign "C:echidna_version, libechidna"
prim__version : PrimIO Bits64

||| Get version as string
export
version : IO String
version = do
  ptr <- primIO prim__version
  pure (prim__getString ptr)

||| Get library build info
export
%foreign "C:echidna_build_info, libechidna"
prim__buildInfo : PrimIO Bits64

||| Get build information
export
buildInfo : IO String
buildInfo = do
  ptr <- primIO prim__buildInfo
  pure (prim__getString ptr)

--------------------------------------------------------------------------------
-- Callback Support
--------------------------------------------------------------------------------

||| Callback function type (C ABI)
|||
||| The C side expects: void (*callback)(uint64_t handle, uint32_t event)
||| We declare the foreign function with the concrete function type
||| so Idris2 can marshal the callback directly without believe_me.
public export
Callback : Type
Callback = Bits64 -> Bits32 -> Bits32

||| Register a callback (typed foreign declaration)
||| The Idris2 FFI marshals function pointers directly when the
||| foreign declaration uses the concrete function type.
export
%foreign "C:echidna_register_callback, libechidna"
prim__registerCallback : Bits64 -> (Bits64 -> Bits32 -> Bits32) -> PrimIO Bits32

||| Safe callback registration
export
registerCallback : Handle -> Callback -> IO (Either Result ())
registerCallback h cb = do
  result <- primIO (prim__registerCallback (handlePtr h) cb)
  pure $ case resultFromInt result of
    Just Ok => Right ()
    Just err => Left err
    Nothing => Left Error
  where
    resultFromInt : Bits32 -> Maybe Result
    resultFromInt 0 = Just Ok
    resultFromInt _ = Just Error

--------------------------------------------------------------------------------
-- Utility Functions
--------------------------------------------------------------------------------

||| Check if library is initialized
export
%foreign "C:echidna_is_initialized, libechidna"
prim__isInitialized : Bits64 -> PrimIO Bits32

||| Check initialization status
export
isInitialized : Handle -> IO Bool
isInitialized h = do
  result <- primIO (prim__isInitialized (handlePtr h))
  pure (result /= 0)
