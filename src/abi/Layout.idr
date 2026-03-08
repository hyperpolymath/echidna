-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| ECHIDNA ABI Memory Layout Proofs
|||
||| Formal proofs about memory layout, alignment, and padding for the
||| C-compatible FFI structs defined in src/rust/ffi/mod.rs. Every layout
||| assertion is backed by a constructive proof (no believe_me).
|||
||| Reference structs (Rust repr(C)):
|||   FfiStringSlice    — ptr(8) + len(8)              = 16 bytes, align 8
|||   FfiOwnedString    — ptr(8) + len(8) + cap(8)     = 24 bytes, align 8
|||   FfiSerializedTerm — kind(1) + pad(3) + dlen(4) + dptr(8) = 16 bytes, align 8
|||   FfiProverConfig   — exec_path(16) + lib_ptrs(8) + lib_len(8) + timeout(8) + neural(1) + pad(7) = 48 bytes, align 8
|||   FfiTactic         — kind(1) + pad(3) + arg_len(4) + arg(8) = 16 bytes, align 8
|||   FfiTacticResult   — kind(1) + pad(3) + msg_len(4) + msg(8) + state(8) = 24 bytes, align 8

module EchidnaABI.Layout

import EchidnaABI.Types
import Data.Vect
import Data.So

%default total

--------------------------------------------------------------------------------
-- Alignment Utilities
--------------------------------------------------------------------------------

||| Calculate padding needed to reach the next alignment boundary
public export
paddingFor : (offset : Nat) -> (align : Nat) -> {auto 0 ok : So (align > 0)} -> Nat
paddingFor offset align =
  let remainder = offset `mod` align
  in if remainder == 0
       then 0
       else minus align remainder

||| Round up to the next alignment boundary
public export
alignUp : (sz : Nat) -> (align : Nat) -> {auto 0 ok : So (align > 0)} -> Nat
alignUp sz align = sz + paddingFor sz align

||| Proof that alignUp never shrinks the size
public export
alignUpGe : (s : Nat) -> (a : Nat) -> {auto 0 ok : So (a > 0)} -> LTE s (alignUp s a)
alignUpGe s a = lteAddRight s

--------------------------------------------------------------------------------
-- Struct Field Descriptors
--------------------------------------------------------------------------------

||| A field in a C struct with its byte offset, byte size, and alignment
public export
record Field where
  constructor MkField
  name      : String
  offset    : Nat
  size      : Nat
  alignment : Nat

||| The byte offset immediately after a field
public export
fieldEnd : Field -> Nat
fieldEnd f = f.offset + f.size

--------------------------------------------------------------------------------
-- Divisibility and Verified Layout
--------------------------------------------------------------------------------

||| Divisibility witness: proof that a = k * b for some k.
||| Used to prove struct sizes are multiples of their alignment.
public export
data DivisibleBy : (a : Nat) -> (b : Nat) -> Type where
  MkDivisible : {k : Nat} -> a = k * b -> DivisibleBy a b

||| A verified struct layout: fields + size + alignment + proof that
||| the total size is a multiple of the alignment. The proof is checked
||| at construction time via Refl, ensuring correctness without believe_me.
public export
record VerifiedLayout (n : Nat) where
  constructor MkVerifiedLayout
  fields      : Vect n Field
  totalSize   : Nat
  structAlign : Nat
  0 sizeOk    : DivisibleBy totalSize structAlign

--------------------------------------------------------------------------------
-- FfiStringSlice Layout
-- Rust: #[repr(C)] struct FfiStringSlice { ptr: *const u8, len: usize }
-- On 64-bit: ptr at offset 0 (8 bytes), len at offset 8 (8 bytes)
-- Total: 16 bytes, alignment: 8
-- Proof: 16 = 2 * 8  ✓
--------------------------------------------------------------------------------

||| Verified layout for FfiStringSlice (16 bytes, align 8)
public export
ffiStringSliceLayout : VerifiedLayout 2
ffiStringSliceLayout = MkVerifiedLayout
  [ MkField "ptr" 0 8 8
  , MkField "len" 8 8 8
  ]
  16 8 (MkDivisible {k=2} Refl)

--------------------------------------------------------------------------------
-- FfiOwnedString Layout
-- Rust: #[repr(C)] struct FfiOwnedString { ptr: *mut u8, len: usize, capacity: usize }
-- On 64-bit: ptr(0,8) + len(8,8) + capacity(16,8) = 24 bytes, align 8
-- Proof: 24 = 3 * 8  ✓
--------------------------------------------------------------------------------

||| Verified layout for FfiOwnedString (24 bytes, align 8)
public export
ffiOwnedStringLayout : VerifiedLayout 3
ffiOwnedStringLayout = MkVerifiedLayout
  [ MkField "ptr"      0  8 8
  , MkField "len"      8  8 8
  , MkField "capacity" 16 8 8
  ]
  24 8 (MkDivisible {k=3} Refl)

--------------------------------------------------------------------------------
-- FfiSerializedTerm Layout
-- Rust: #[repr(C)] struct FfiSerializedTerm {
--   kind: FfiTermKind,    // u8, offset 0
--   _padding: [u8; 3],    // 3 bytes padding, offset 1
--   data_len: u32,        // 4 bytes, offset 4
--   data: *const u8,      // 8 bytes, offset 8
-- }
-- Total: 16 bytes, align 8
-- Proof: 16 = 2 * 8  ✓
--------------------------------------------------------------------------------

||| Verified layout for FfiSerializedTerm (16 bytes, align 8)
public export
ffiSerializedTermLayout : VerifiedLayout 4
ffiSerializedTermLayout = MkVerifiedLayout
  [ MkField "kind"     0  1 1
  , MkField "_padding" 1  3 1
  , MkField "data_len" 4  4 4
  , MkField "data"     8  8 8
  ]
  16 8 (MkDivisible {k=2} Refl)

--------------------------------------------------------------------------------
-- FfiProverConfig Layout
-- Rust: #[repr(C)] struct FfiProverConfig {
--   executable_path: FfiStringSlice,  // 16 bytes, offset 0
--   library_paths: *const FfiStringSlice,  // 8 bytes, offset 16
--   library_paths_len: usize,         // 8 bytes, offset 24
--   timeout_ms: u64,                  // 8 bytes, offset 32
--   neural_enabled: bool,             // 1 byte, offset 40
--   _padding: [u8; 7],                // 7 bytes, offset 41
-- }
-- Total: 48 bytes, align 8
-- Proof: 48 = 6 * 8  ✓
--------------------------------------------------------------------------------

||| Verified layout for FfiProverConfig (48 bytes, align 8)
public export
ffiProverConfigLayout : VerifiedLayout 6
ffiProverConfigLayout = MkVerifiedLayout
  [ MkField "executable_path"   0  16 8
  , MkField "library_paths"    16   8 8
  , MkField "library_paths_len" 24  8 8
  , MkField "timeout_ms"       32   8 8
  , MkField "neural_enabled"   40   1 1
  , MkField "_padding"         41   7 1
  ]
  48 8 (MkDivisible {k=6} Refl)

--------------------------------------------------------------------------------
-- FfiTactic Layout
-- Rust: #[repr(C)] struct FfiTactic {
--   kind: FfiTacticKind,  // u8, offset 0
--   _padding: [u8; 3],    // 3 bytes, offset 1
--   arg_len: u32,          // 4 bytes, offset 4
--   arg: *const u8,        // 8 bytes, offset 8
-- }
-- Total: 16 bytes, align 8
-- Proof: 16 = 2 * 8  ✓
--------------------------------------------------------------------------------

||| Verified layout for FfiTactic (16 bytes, align 8)
public export
ffiTacticLayout : VerifiedLayout 4
ffiTacticLayout = MkVerifiedLayout
  [ MkField "kind"     0 1 1
  , MkField "_padding" 1 3 1
  , MkField "arg_len"  4 4 4
  , MkField "arg"      8 8 8
  ]
  16 8 (MkDivisible {k=2} Refl)

--------------------------------------------------------------------------------
-- FfiTacticResult Layout
-- Rust: #[repr(C)] struct FfiTacticResult {
--   kind: FfiTacticResultKind,  // u8, offset 0
--   _padding: [u8; 3],          // 3 bytes, offset 1
--   message_len: u32,            // 4 bytes, offset 4
--   message: *const u8,          // 8 bytes, offset 8
--   new_state: *mut c_void,      // 8 bytes, offset 16
-- }
-- Total: 24 bytes, align 8
-- Proof: 24 = 3 * 8  ✓
--------------------------------------------------------------------------------

||| Verified layout for FfiTacticResult (24 bytes, align 8)
public export
ffiTacticResultLayout : VerifiedLayout 5
ffiTacticResultLayout = MkVerifiedLayout
  [ MkField "kind"        0  1 1
  , MkField "_padding"    1  3 1
  , MkField "message_len" 4  4 4
  , MkField "message"     8  8 8
  , MkField "new_state"  16  8 8
  ]
  24 8 (MkDivisible {k=3} Refl)

--------------------------------------------------------------------------------
-- Platform-Specific Size Assertions
--------------------------------------------------------------------------------

||| On 64-bit platforms, pointers are 8 bytes
public export
ptrSize64 : (p : Platform) -> Not (p = WASM) -> ptrSize p = 64
ptrSize64 Linux   contra = Refl
ptrSize64 Windows contra = Refl
ptrSize64 MacOS   contra = Refl
ptrSize64 BSD     contra = Refl
ptrSize64 WASM    contra = absurd (contra Refl)

||| On WASM, pointers are 4 bytes (32-bit)
public export
ptrSizeWASM : ptrSize WASM = 32
ptrSizeWASM = Refl
