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
paddingFor : (offset : Nat) -> (alignment : Nat) -> {auto 0 ok : So (alignment > 0)} -> Nat
paddingFor offset alignment =
  let remainder = offset `mod` alignment
  in if remainder == 0
       then 0
       else alignment - remainder

||| Round up to the next alignment boundary
public export
alignUp : (size : Nat) -> (alignment : Nat) -> {auto 0 ok : So (alignment > 0)} -> Nat
alignUp size alignment = size + paddingFor size alignment

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
-- Struct Layout
--------------------------------------------------------------------------------

||| A complete struct layout: an ordered list of fields, a total size,
||| and an overall alignment.
public export
record StructLayout (n : Nat) where
  constructor MkStructLayout
  fields    : Vect n Field
  totalSize : Nat
  alignment : Nat

||| Proof that every field lies within the struct's total size
public export
data AllFieldsInBounds : StructLayout n -> Type where
  BoundsNil  : AllFieldsInBounds (MkStructLayout [] size align)
  BoundsCons :
    {0 f : Field} -> {0 fs : Vect k Field} ->
    So (f.offset + f.size <= totalSize layout) ->
    AllFieldsInBounds (MkStructLayout fs (totalSize layout) (alignment layout)) ->
    AllFieldsInBounds (MkStructLayout (f :: fs) (totalSize layout) (alignment layout))

||| Proof that every field's offset is aligned to its own alignment
public export
data AllFieldsAligned : Vect n Field -> Type where
  AlignedNil  : AllFieldsAligned []
  AlignedCons :
    {0 f : Field} -> {0 fs : Vect k Field} ->
    So (f.offset `mod` f.alignment == 0) ->
    AllFieldsAligned fs ->
    AllFieldsAligned (f :: fs)

||| Proof that a struct's total size is a multiple of its alignment
public export
data SizeAligned : StructLayout n -> Type where
  MkSizeAligned : So (totalSize layout `mod` alignment layout == 0) -> SizeAligned layout

||| A struct layout that satisfies all C ABI rules
public export
data CABICompliant : StructLayout n -> Type where
  MkCABICompliant :
    {0 layout : StructLayout n} ->
    AllFieldsAligned (fields layout) ->
    SizeAligned layout ->
    CABICompliant layout

--------------------------------------------------------------------------------
-- FfiStringSlice Layout
-- Rust: #[repr(C)] struct FfiStringSlice { ptr: *const u8, len: usize }
-- On 64-bit: ptr at offset 0 (8 bytes), len at offset 8 (8 bytes)
-- Total: 16 bytes, alignment: 8
--------------------------------------------------------------------------------

||| Field layout for FfiStringSlice
public export
ffiStringSliceFields : Vect 2 Field
ffiStringSliceFields =
  [ MkField "ptr" 0 8 8
  , MkField "len" 8 8 8
  ]

||| FfiStringSlice struct layout: 16 bytes, align 8
public export
ffiStringSliceLayout : StructLayout 2
ffiStringSliceLayout = MkStructLayout ffiStringSliceFields 16 8

||| Proof that FfiStringSlice fields are properly aligned
public export
ffiStringSliceFieldsAligned : AllFieldsAligned ffiStringSliceFields
ffiStringSliceFieldsAligned = AlignedCons Oh (AlignedCons Oh AlignedNil)

||| Proof that FfiStringSlice total size is aligned
public export
ffiStringSliceSizeAligned : SizeAligned ffiStringSliceLayout
ffiStringSliceSizeAligned = MkSizeAligned Oh

||| Full C ABI compliance proof for FfiStringSlice
public export
ffiStringSliceCABI : CABICompliant ffiStringSliceLayout
ffiStringSliceCABI = MkCABICompliant ffiStringSliceFieldsAligned ffiStringSliceSizeAligned

||| Proof that FfiStringSlice is exactly 16 bytes
public export
ffiStringSliceSize16 : totalSize ffiStringSliceLayout = 16
ffiStringSliceSize16 = Refl

||| Proof that FfiStringSlice alignment is 8
public export
ffiStringSliceAlign8 : alignment ffiStringSliceLayout = 8
ffiStringSliceAlign8 = Refl

--------------------------------------------------------------------------------
-- FfiOwnedString Layout
-- Rust: #[repr(C)] struct FfiOwnedString { ptr: *mut u8, len: usize, capacity: usize }
-- On 64-bit: ptr(0,8) + len(8,8) + capacity(16,8) = 24 bytes, align 8
--------------------------------------------------------------------------------

||| Field layout for FfiOwnedString
public export
ffiOwnedStringFields : Vect 3 Field
ffiOwnedStringFields =
  [ MkField "ptr"      0  8 8
  , MkField "len"      8  8 8
  , MkField "capacity" 16 8 8
  ]

||| FfiOwnedString struct layout: 24 bytes, align 8
public export
ffiOwnedStringLayout : StructLayout 3
ffiOwnedStringLayout = MkStructLayout ffiOwnedStringFields 24 8

||| Fields are properly aligned
public export
ffiOwnedStringFieldsAligned : AllFieldsAligned ffiOwnedStringFields
ffiOwnedStringFieldsAligned = AlignedCons Oh (AlignedCons Oh (AlignedCons Oh AlignedNil))

||| Total size is aligned
public export
ffiOwnedStringSizeAligned : SizeAligned ffiOwnedStringLayout
ffiOwnedStringSizeAligned = MkSizeAligned Oh

||| Full C ABI compliance proof for FfiOwnedString
public export
ffiOwnedStringCABI : CABICompliant ffiOwnedStringLayout
ffiOwnedStringCABI = MkCABICompliant ffiOwnedStringFieldsAligned ffiOwnedStringSizeAligned

||| Proof that FfiOwnedString is exactly 24 bytes
public export
ffiOwnedStringSize24 : totalSize ffiOwnedStringLayout = 24
ffiOwnedStringSize24 = Refl

--------------------------------------------------------------------------------
-- FfiSerializedTerm Layout
-- Rust: #[repr(C)] struct FfiSerializedTerm {
--   kind: FfiTermKind,    // u8, offset 0
--   _padding: [u8; 3],    // 3 bytes padding, offset 1
--   data_len: u32,        // 4 bytes, offset 4
--   data: *const u8,      // 8 bytes, offset 8
-- }
-- Total: 16 bytes, align 8
--------------------------------------------------------------------------------

||| Field layout for FfiSerializedTerm
public export
ffiSerializedTermFields : Vect 4 Field
ffiSerializedTermFields =
  [ MkField "kind"     0  1 1
  , MkField "_padding" 1  3 1
  , MkField "data_len" 4  4 4
  , MkField "data"     8  8 8
  ]

||| FfiSerializedTerm struct layout: 16 bytes, align 8
public export
ffiSerializedTermLayout : StructLayout 4
ffiSerializedTermLayout = MkStructLayout ffiSerializedTermFields 16 8

||| Fields are properly aligned
public export
ffiSerializedTermFieldsAligned : AllFieldsAligned ffiSerializedTermFields
ffiSerializedTermFieldsAligned =
  AlignedCons Oh   -- kind at 0, align 1: 0 mod 1 == 0
  (AlignedCons Oh  -- _padding at 1, align 1: 1 mod 1 == 0
  (AlignedCons Oh  -- data_len at 4, align 4: 4 mod 4 == 0
  (AlignedCons Oh  -- data at 8, align 8: 8 mod 8 == 0
  AlignedNil)))

||| Total size is aligned
public export
ffiSerializedTermSizeAligned : SizeAligned ffiSerializedTermLayout
ffiSerializedTermSizeAligned = MkSizeAligned Oh

||| Full C ABI compliance proof for FfiSerializedTerm
public export
ffiSerializedTermCABI : CABICompliant ffiSerializedTermLayout
ffiSerializedTermCABI = MkCABICompliant ffiSerializedTermFieldsAligned ffiSerializedTermSizeAligned

||| Proof that FfiSerializedTerm is exactly 16 bytes
public export
ffiSerializedTermSize16 : totalSize ffiSerializedTermLayout = 16
ffiSerializedTermSize16 = Refl

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
--------------------------------------------------------------------------------

||| Field layout for FfiProverConfig
public export
ffiProverConfigFields : Vect 6 Field
ffiProverConfigFields =
  [ MkField "executable_path"   0  16 8
  , MkField "library_paths"    16   8 8
  , MkField "library_paths_len" 24  8 8
  , MkField "timeout_ms"       32   8 8
  , MkField "neural_enabled"   40   1 1
  , MkField "_padding"         41   7 1
  ]

||| FfiProverConfig struct layout: 48 bytes, align 8
public export
ffiProverConfigLayout : StructLayout 6
ffiProverConfigLayout = MkStructLayout ffiProverConfigFields 48 8

||| Fields are properly aligned
public export
ffiProverConfigFieldsAligned : AllFieldsAligned ffiProverConfigFields
ffiProverConfigFieldsAligned =
  AlignedCons Oh   -- executable_path at 0, align 8
  (AlignedCons Oh  -- library_paths at 16, align 8
  (AlignedCons Oh  -- library_paths_len at 24, align 8
  (AlignedCons Oh  -- timeout_ms at 32, align 8
  (AlignedCons Oh  -- neural_enabled at 40, align 1
  (AlignedCons Oh  -- _padding at 41, align 1
  AlignedNil)))))

||| Total size is aligned
public export
ffiProverConfigSizeAligned : SizeAligned ffiProverConfigLayout
ffiProverConfigSizeAligned = MkSizeAligned Oh

||| Full C ABI compliance proof for FfiProverConfig
public export
ffiProverConfigCABI : CABICompliant ffiProverConfigLayout
ffiProverConfigCABI = MkCABICompliant ffiProverConfigFieldsAligned ffiProverConfigSizeAligned

||| Proof that FfiProverConfig is exactly 48 bytes
public export
ffiProverConfigSize48 : totalSize ffiProverConfigLayout = 48
ffiProverConfigSize48 = Refl

--------------------------------------------------------------------------------
-- FfiTactic Layout
-- Rust: #[repr(C)] struct FfiTactic {
--   kind: FfiTacticKind,  // u8, offset 0
--   _padding: [u8; 3],    // 3 bytes, offset 1
--   arg_len: u32,          // 4 bytes, offset 4
--   arg: *const u8,        // 8 bytes, offset 8
-- }
-- Total: 16 bytes, align 8
--------------------------------------------------------------------------------

||| Field layout for FfiTactic
public export
ffiTacticFields : Vect 4 Field
ffiTacticFields =
  [ MkField "kind"     0 1 1
  , MkField "_padding" 1 3 1
  , MkField "arg_len"  4 4 4
  , MkField "arg"      8 8 8
  ]

||| FfiTactic struct layout: 16 bytes, align 8
public export
ffiTacticLayout : StructLayout 4
ffiTacticLayout = MkStructLayout ffiTacticFields 16 8

||| Fields are properly aligned
public export
ffiTacticFieldsAligned : AllFieldsAligned ffiTacticFields
ffiTacticFieldsAligned =
  AlignedCons Oh (AlignedCons Oh (AlignedCons Oh (AlignedCons Oh AlignedNil)))

||| Total size is aligned
public export
ffiTacticSizeAligned : SizeAligned ffiTacticLayout
ffiTacticSizeAligned = MkSizeAligned Oh

||| Full C ABI compliance proof for FfiTactic
public export
ffiTacticCABI : CABICompliant ffiTacticLayout
ffiTacticCABI = MkCABICompliant ffiTacticFieldsAligned ffiTacticSizeAligned

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
--------------------------------------------------------------------------------

||| Field layout for FfiTacticResult
public export
ffiTacticResultFields : Vect 5 Field
ffiTacticResultFields =
  [ MkField "kind"        0  1 1
  , MkField "_padding"    1  3 1
  , MkField "message_len" 4  4 4
  , MkField "message"     8  8 8
  , MkField "new_state"  16  8 8
  ]

||| FfiTacticResult struct layout: 24 bytes, align 8
public export
ffiTacticResultLayout : StructLayout 5
ffiTacticResultLayout = MkStructLayout ffiTacticResultFields 24 8

||| Fields are properly aligned
public export
ffiTacticResultFieldsAligned : AllFieldsAligned ffiTacticResultFields
ffiTacticResultFieldsAligned =
  AlignedCons Oh (AlignedCons Oh (AlignedCons Oh (AlignedCons Oh (AlignedCons Oh AlignedNil))))

||| Total size is aligned
public export
ffiTacticResultSizeAligned : SizeAligned ffiTacticResultLayout
ffiTacticResultSizeAligned = MkSizeAligned Oh

||| Full C ABI compliance proof for FfiTacticResult
public export
ffiTacticResultCABI : CABICompliant ffiTacticResultLayout
ffiTacticResultCABI = MkCABICompliant ffiTacticResultFieldsAligned ffiTacticResultSizeAligned

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

||| All layouts above assume 64-bit. On WASM (32-bit), pointer fields
||| would be 4 bytes instead of 8, changing struct sizes.
||| This predicate marks a layout as valid for 64-bit only.
public export
data Valid64BitLayout : StructLayout n -> Type where
  MkValid64 : CABICompliant layout -> Valid64BitLayout layout

||| All ECHIDNA FFI layouts are valid on 64-bit platforms
public export
allLayoutsValid64 : ( Valid64BitLayout ffiStringSliceLayout
                    , Valid64BitLayout ffiOwnedStringLayout
                    , Valid64BitLayout ffiSerializedTermLayout
                    , Valid64BitLayout ffiProverConfigLayout
                    , Valid64BitLayout ffiTacticLayout
                    , Valid64BitLayout ffiTacticResultLayout
                    )
allLayoutsValid64 =
  ( MkValid64 ffiStringSliceCABI
  , MkValid64 ffiOwnedStringCABI
  , MkValid64 ffiSerializedTermCABI
  , MkValid64 ffiProverConfigCABI
  , MkValid64 ffiTacticCABI
  , MkValid64 ffiTacticResultCABI
  )
