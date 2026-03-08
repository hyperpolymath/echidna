# ECHIDNA ABI/FFI Documentation

## Overview

ECHIDNA follows the **Hyperpolymath RSR Standard** for ABI and FFI design:

- **ABI (Application Binary Interface)** defined in **Idris2** with formal proofs (zero `believe_me`)
- **FFI (Foreign Function Interface)** implemented in **Zig** for C compatibility
- **Generated C headers** bridge Idris2 ABI to Zig FFI
- **V-lang REST adapters** link shared libraries and expose triple API (REST+gRPC+GraphQL)
- **Any language** can call through standard C ABI

## Architecture

```
┌──────────────────────────────────────────────────────────────┐
│  ABI Definitions (Idris2) — 7 modules                       │
│  src/abi/                                                    │
│  - Types.idr       (30 provers, enums, Handle, proofs)       │
│  - Layout.idr      (Memory layout: DivisibleBy, VerifiedLayout)│
│  - Foreign.idr     (Core FFI declarations)                   │
│  - Overlay.idr     (Tor/IPFS/Ethereum types)                 │
│  - Overlay/Foreign.idr (Overlay FFI declarations)            │
│  - Boj/Foreign.idr (BoJ cartridge FFI)                       │
│  - TypeLL/Foreign.idr (TypeLL FFI)                           │
└─────────────────────────┬────────────────────────────────────┘
                          │
                          │ defines types / generates headers
                          ▼
┌──────────────────────────────────────────────────────────────┐
│  C Headers (generated)                                       │
│  generated/abi/                                              │
│  - echidna_ffi.h      (23 functions, 5 enums, 4 callbacks)  │
│  - echidna_overlay.h  (Tor/IPFS/Ethereum C interface)        │
│  - echidna_boj.h      (BoJ cartridge C interface)            │
│  - echidna_typell.h   (TypeLL C interface)                   │
└─────────────────────────┬────────────────────────────────────┘
                          │
                          │ imported by
                          ▼
┌──────────────────────────────────────────────────────────────┐
│  FFI Implementation (Zig) — 4 modules                        │
│  ffi/zig/src/                                                │
│  - core.zig       → libechidna_ffi.so     (prover mgmt)     │
│  - overlay.zig    → libechidna_overlay.so (Tor/IPFS/Eth)    │
│  - boj.zig        → libechidna_boj.so    (BoJ cartridges)   │
│  - typell.zig     → libechidna_typell.so (TypeLL types)      │
│  All: pub export fn (dual Zig @import + C linker access)     │
│  All: bidirectional callback registration                    │
└─────────────────────────┬────────────────────────────────────┘
                          │
                          │ linked by
                          ▼
┌──────────────────────────────────────────────────────────────┐
│  V-lang REST Adapters                                        │
│  src/interfaces/v-adapter/                                   │
│  - core.v    (ports 8100-8102: REST, gRPC, GraphQL)          │
│  - overlay.v (port 8103)                                     │
│  - boj.v     (port 7700)                                     │
│  - typell.v  (port 7800)                                     │
└─────────────────────────┬────────────────────────────────────┘
                          │
                          │ consumed by
                          ▼
┌──────────────────────────────────────────────────────────────┐
│  Any Language via C ABI                                      │
│  - Rust, ReScript, Julia, V, etc.                            │
└──────────────────────────────────────────────────────────────┘
```

## Directory Structure

```
echidna/
├── src/
│   ├── abi/                          # ABI definitions (Idris2)
│   │   ├── Types.idr                  # Core types: 30 ProverKind, Handle, FfiStatus, proofs
│   │   ├── Layout.idr                 # Memory layout: DivisibleBy, VerifiedLayout, 6 structs
│   │   ├── Foreign.idr                # Core FFI function declarations
│   │   ├── Overlay.idr                # Overlay types: Tor, IPFS, Ethereum
│   │   ├── Overlay/Foreign.idr        # Overlay FFI declarations
│   │   ├── Boj/Foreign.idr            # BoJ cartridge FFI declarations
│   │   └── TypeLL/Foreign.idr         # TypeLL FFI declarations
│   └── interfaces/
│       └── v-adapter/                 # V-lang REST adapters
│           ├── core.v                 # Core adapter (ports 8100-8102)
│           ├── overlay.v              # Overlay adapter (port 8103)
│           ├── boj.v                  # BoJ adapter (port 7700)
│           └── typell.v               # TypeLL adapter (port 7800)
│
├── ffi/
│   └── zig/                           # FFI implementation (Zig)
│       ├── build.zig                  # Build config (4 libraries, test steps)
│       ├── build.zig.zon              # Dependencies
│       ├── src/
│       │   ├── core.zig               # Core prover FFI → libechidna_ffi.so
│       │   ├── overlay.zig            # Overlay FFI → libechidna_overlay.so
│       │   ├── boj.zig                # BoJ FFI → libechidna_boj.so
│       │   └── typell.zig             # TypeLL FFI → libechidna_typell.so
│       └── test/
│           ├── core_native_test.zig   # 30 pure Zig tests via @import("core")
│           └── overlay_native_test.zig # Overlay native tests
│
└── generated/                         # Auto-generated files
    └── abi/
        ├── echidna_ffi.h              # Core C header (23 fn, 5 enum, 4 callbacks)
        ├── echidna_overlay.h          # Overlay C header
        ├── echidna_boj.h              # BoJ C header
        └── echidna_typell.h           # TypeLL C header
```

## Idris2 ABI Proofs

### Memory Layout Verification

All 6 struct layouts are formally verified using `DivisibleBy` witnesses:

```idris
data DivisibleBy : (a : Nat) -> (b : Nat) -> Type where
  MkDivisible : {k : Nat} -> a = k * b -> DivisibleBy a b

record VerifiedLayout (n : Nat) where
  constructor MkVerifiedLayout
  fields      : Vect n Field
  totalSize   : Nat
  structAlign : Nat
  0 sizeOk    : DivisibleBy totalSize structAlign

-- Example: FfiStringSlice (16 bytes, align 8)
-- Proof: 16 = 2 * 8 via Refl at construction time
ffiStringSliceLayout : VerifiedLayout 2
ffiStringSliceLayout = MkVerifiedLayout
  [ MkField "ptr" 0 8 8, MkField "len" 8 8 8 ]
  16 8 (MkDivisible {k=2} Refl)
```

### Non-Null Handle Guarantee

```idris
data Handle : Type where
  MkHandle : (ptr : Bits64) -> (0 nonNull : So (not (ptr == 0))) -> Handle

createHandle : Bits64 -> Maybe Handle
createHandle ptr with (choose (not (ptr == 0)))
  createHandle ptr | Left  prf = Just (MkHandle ptr prf)
  createHandle ptr | Right _   = Nothing
```

### Round-Trip Enum Proofs

```idris
overlayKindRoundTrip : (k : OverlayKind) -> overlayKindFromInt (overlayKindToInt k) = Just k
overlayKindRoundTrip Tor      = Refl
overlayKindRoundTrip IPFS     = Refl
overlayKindRoundTrip Ethereum = Refl
```

## Zig FFI Features

### Dual Export Mode

All FFI functions use `pub export fn` for both Zig `@import` and C linker access:

```zig
pub export fn echidna_prover_init(kind: u8) callconv(.C) i32 {
    // Available via both @import("core") and C linking
}
```

### Bidirectional Callbacks

Each module supports registering callbacks for real-time events:

```zig
// Core callbacks
pub export fn echidna_set_init_callback(cb: ?*const fn () callconv(.C) void) callconv(.C) void;
pub export fn echidna_set_prover_change_callback(cb: ?*const fn (u8) callconv(.C) void) callconv(.C) void;
pub export fn echidna_set_error_callback(cb: ?*const fn ([*]const u8, usize) callconv(.C) void) callconv(.C) void;
pub export fn echidna_set_verify_complete_callback(cb: ?*const fn (i32) callconv(.C) void) callconv(.C) void;
```

## Building

### Build All Libraries

```bash
cd ffi/zig
zig build                         # Build debug (4 .so files)
zig build -Doptimize=ReleaseFast  # Build optimized
```

### Run Tests

```bash
cd ffi/zig
zig build test                    # All Zig tests
zig build test-core-native        # Core native tests (30 tests)
zig build test-overlay-native     # Overlay native tests
```

### Type-Check Idris2 ABI

```bash
# Individual module checking
idris2 --check src/abi/Types.idr
idris2 --check src/abi/Layout.idr
idris2 --check src/abi/Foreign.idr
```

### Cross-Compile

```bash
cd ffi/zig
zig build -Dtarget=x86_64-linux
zig build -Dtarget=aarch64-macos
zig build -Dtarget=x86_64-windows
```

## Usage

### From C

```c
#include "echidna_ffi.h"

void on_error(const char* msg, size_t len) {
    fprintf(stderr, "Error: %.*s\n", (int)len, msg);
}

int main() {
    echidna_set_error_callback(on_error);

    int status = echidna_prover_init(0);  // Agda
    if (status != 0) return 1;

    // ... use prover ...

    echidna_prover_shutdown();
    return 0;
}
```

Compile with:
```bash
gcc -o example example.c -lechidna_ffi -L./ffi/zig/zig-out/lib
```

### From Rust

```rust
#[link(name = "echidna_ffi")]
extern "C" {
    fn echidna_prover_init(kind: u8) -> i32;
    fn echidna_prover_shutdown();
    fn echidna_set_error_callback(
        cb: Option<extern "C" fn(*const u8, usize)>,
    );
}
```

### From Julia

```julia
const libechidna = "libechidna_ffi"

function prover_init(kind::UInt8)
    ccall((:echidna_prover_init, libechidna), Cint, (UInt8,), kind)
end

function prover_shutdown()
    ccall((:echidna_prover_shutdown, libechidna), Cvoid, ())
end
```

## Testing

### Native Zig Tests (30+)

```bash
cd ffi/zig
zig build test-core-native        # Tests: enum values, StringSlice, safe API,
                                  #        C-ABI exports, callbacks, round-trips
zig build test-overlay-native     # Tests: overlay status, Tor/IPFS/Eth types
```

### ABI Verification (Idris2)

All proofs are checked at compile time. Type-checking the ABI modules verifies:
- Struct sizes are multiples of their alignment (DivisibleBy witnesses)
- Handle pointers are non-null (So proofs)
- Enum round-trips are lossless (Refl proofs)
- Platform pointer sizes are correct (ptrSize64, ptrSizeWASM)

## Contributing

When modifying the ABI/FFI:

1. **Update ABI first** (`src/abi/*.idr`)
   - Modify type definitions
   - Update/add proofs
   - Ensure backward compatibility

2. **Update C headers** (`generated/abi/echidna_*.h`)
   - Match new types and functions

3. **Update FFI implementation** (`ffi/zig/src/*.zig`)
   - Implement new exported functions
   - Match ABI types exactly
   - Add callback support if needed

4. **Add tests**
   - Native Zig tests in `ffi/zig/test/`
   - Build step in `build.zig`

5. **Update V-lang adapters** (`src/interfaces/v-adapter/*.v`)
   - Add REST endpoints for new FFI functions
   - Update extern declarations

## License

PMPL-1.0-or-later

## See Also

- [Idris2 Documentation](https://idris2.readthedocs.io)
- [Zig Documentation](https://ziglang.org/documentation/master/)
- [Rhodium Standard Repositories](https://github.com/hyperpolymath/rhodium-standard-repositories)
