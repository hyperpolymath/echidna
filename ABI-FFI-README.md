{{~ Aditionally delete this line and fill out the template below ~}}

# {{PROJECT}} ABI/FFI Documentation

## Overview

This library follows the **Hyperpolymath RSR Standard** for ABI and FFI design:

- **ABI (Application Binary Interface)** defined in **Idris2** with formal proofs
- **FFI (Foreign Function Interface)** implemented in **Zig** for C compatibility
- **Generated C headers** bridge Idris2 ABI to Zig FFI
- **Any language** can call through standard C ABI

## Architecture

```
┌─────────────────────────────────────────────┐
│  ABI Definitions (Idris2)                   │
│  src/abi/                                   │
│  - Types.idr      (Type definitions)        │
│  - Layout.idr     (Memory layout proofs)    │
│  - Foreign.idr    (FFI declarations)        │
└─────────────────┬───────────────────────────┘
                  │
                  │ generates (at compile time)
                  ▼
┌─────────────────────────────────────────────┐
│  C Headers (auto-generated)                 │
│  generated/abi/{{project}}.h                │
└─────────────────┬───────────────────────────┘
                  │
                  │ imported by
                  ▼
┌─────────────────────────────────────────────┐
│  FFI Implementation (Zig)                   │
│  ffi/zig/src/main.zig                       │
│  - Implements C-compatible functions        │
│  - Zero-cost abstractions                   │
│  - Memory-safe by default                   │
└─────────────────┬───────────────────────────┘
                  │
                  │ compiled to lib{{project}}.so/.a
                  ▼
┌─────────────────────────────────────────────┐
│  Any Language via C ABI                     │
│  - Rust, ReScript, Julia, Python, etc.     │
└─────────────────────────────────────────────┘
```

## Directory Structure

```
{{project}}/
├── src/
│   ├── abi/                    # ABI definitions (Idris2)
│   │   ├── Types.idr           # Core type definitions with proofs
│   │   ├── Layout.idr          # Memory layout verification
│   │   └── Foreign.idr         # FFI function declarations
│   └── lib/                    # Core library (any language)
│
├── ffi/
│   └── zig/                    # FFI implementation (Zig)
│       ├── build.zig           # Build configuration
│       ├── build.zig.zon       # Dependencies
│       ├── src/
│       │   └── main.zig        # C-compatible FFI implementation
│       ├── test/
│       │   └── integration_test.zig
│       └── include/
│           └── {{project}}.h   # C header (optional, can be generated)
│
├── generated/                  # Auto-generated files
│   └── abi/
│       └── {{project}}.h       # Generated from Idris2 ABI
│
└── bindings/                   # Language-specific wrappers (optional)
    ├── rust/
    ├── rescript/
    └── julia/
```

## Why Idris2 for ABI?

### 1. **Formal Verification**

Idris2's dependent types allow proving properties about the ABI at compile-time:

```idris
-- Prove struct size is correct
public export
exampleStructSize : HasSize ExampleStruct 16

-- Prove field alignment is correct
public export
fieldAligned : Divides 8 (offsetOf ExampleStruct.field)

-- Prove ABI is platform-compatible
public export
abiCompatible : Compatible (ABI 1) (ABI 2)
```

### 2. **Type Safety**

Encode invariants that C/Zig cannot express:

```idris
-- Non-null pointer guaranteed at type level
data Handle : Type where
  MkHandle : (ptr : Bits64) -> {auto 0 nonNull : So (ptr /= 0)} -> Handle

-- Array with length proof
data Buffer : (n : Nat) -> Type where
  MkBuffer : Vect n Byte -> Buffer n
```

### 3. **Platform Abstraction**

Platform-specific types with compile-time selection:

```idris
CInt : Platform -> Type
CInt Linux = Bits32
CInt Windows = Bits32

CSize : Platform -> Type
CSize Linux = Bits64
CSize Windows = Bits64
```

### 4. **Safe Evolution**

Prove that new ABI versions are backward-compatible:

```idris
-- Compiler enforces compatibility
abiUpgrade : ABI 1 -> ABI 2
abiUpgrade old = MkABI2 {
  -- Must preserve all v1 fields
  v1_compat = old,
  -- Can add new fields
  new_features = defaults
}
```

## Why Zig for FFI?

### 1. **C ABI Compatibility**

Zig exports C-compatible functions naturally:

```zig
export fn library_function(param: i32) i32 {
    return param * 2;
}
```

### 2. **Memory Safety**

Compile-time safety without runtime overhead:

```zig
// Null check enforced at compile time
const handle = init() orelse return error.InitFailed;
defer free(handle);
```

### 3. **Cross-Compilation**

Built-in cross-compilation to any platform:

```bash
zig build -Dtarget=x86_64-linux
zig build -Dtarget=aarch64-macos
zig build -Dtarget=x86_64-windows
```

### 4. **Zero Dependencies**

No runtime, no libc required (unless explicitly needed):

```zig
// Minimal binary size
pub const lib = @import("std");
// Only includes what you use
```

## Building

### Build FFI Library

```bash
cd ffi/zig
zig build                         # Build debug
zig build -Doptimize=ReleaseFast  # Build optimized
zig build test                    # Run tests
```

### Generate C Header from Idris2 ABI

```bash
cd src/abi
idris2 --cg c-header Types.idr -o ../../generated/abi/{{project}}.h
```

### Cross-Compile

```bash
cd ffi/zig

# Linux x86_64
zig build -Dtarget=x86_64-linux

# macOS ARM64
zig build -Dtarget=aarch64-macos

# Windows x86_64
zig build -Dtarget=x86_64-windows
```

## Usage

### From C

```c
#include "{{project}}.h"

int main() {
    void* handle = {{project}}_init();
    if (!handle) return 1;

    int result = {{project}}_process(handle, 42);
    if (result != 0) {
        const char* err = {{project}}_last_error();
        fprintf(stderr, "Error: %s\n", err);
    }

    {{project}}_free(handle);
    return 0;
}
```

Compile with:
```bash
gcc -o example example.c -l{{project}} -L./zig-out/lib
```

### From Idris2

```idris
import {{PROJECT}}.ABI.Foreign

main : IO ()
main = do
  Just handle <- init
    | Nothing => putStrLn "Failed to initialize"

  Right result <- process handle 42
    | Left err => putStrLn $ "Error: " ++ errorDescription err

  free handle
  putStrLn "Success"
```

### From Rust

```rust
#[link(name = "{{project}}")]
extern "C" {
    fn {{project}}_init() -> *mut std::ffi::c_void;
    fn {{project}}_free(handle: *mut std::ffi::c_void);
    fn {{project}}_process(handle: *mut std::ffi::c_void, input: u32) -> i32;
}

fn main() {
    unsafe {
        let handle = {{project}}_init();
        assert!(!handle.is_null());

        let result = {{project}}_process(handle, 42);
        assert_eq!(result, 0);

        {{project}}_free(handle);
    }
}
```

### From Julia

```julia
const lib{{project}} = "lib{{project}}"

function init()
    handle = ccall((:{{project}}_init, lib{{project}}), Ptr{Cvoid}, ())
    handle == C_NULL && error("Failed to initialize")
    handle
end

function process(handle, input)
    result = ccall((:{{project}}_process, lib{{project}}), Cint, (Ptr{Cvoid}, UInt32), handle, input)
    result
end

function cleanup(handle)
    ccall((:{{project}}_free, lib{{project}}), Cvoid, (Ptr{Cvoid},), handle)
end

# Usage
handle = init()
try
    result = process(handle, 42)
    println("Result: $result")
finally
    cleanup(handle)
end
```

## Testing

### Unit Tests (Zig)

```bash
cd ffi/zig
zig build test
```

### Integration Tests

```bash
cd ffi/zig
zig build test-integration
```

### ABI Verification (Idris2)

```idris
-- Compile-time verification
%runElab verifyABI

-- Runtime checks
main : IO ()
main = do
  verifyLayoutsCorrect
  verifyAlignmentsCorrect
  putStrLn "ABI verification passed"
```

## Contributing

When modifying the ABI/FFI:

1. **Update ABI first** (`src/abi/*.idr`)
   - Modify type definitions
   - Update proofs
   - Ensure backward compatibility

2. **Generate C header**
   ```bash
   idris2 --cg c-header src/abi/Types.idr -o generated/abi/{{project}}.h
   ```

3. **Update FFI implementation** (`ffi/zig/src/main.zig`)
   - Implement new functions
   - Match ABI types exactly

4. **Add tests**
   - Unit tests in Zig
   - Integration tests
   - ABI verification tests

5. **Update documentation**
   - Function signatures
   - Usage examples
   - Migration guide (if breaking changes)

## License

{{LICENSE}}

## See Also

- [Idris2 Documentation](https://idris2.readthedocs.io)
- [Zig Documentation](https://ziglang.org/documentation/master/)
- [Rhodium Standard Repositories](https://github.com/hyperpolymath/rhodium-standard-repositories)
- [FFI Migration Guide](../ffi-migration-guide.md)
- [ABI Migration Guide](../abi-migration-guide.md)
