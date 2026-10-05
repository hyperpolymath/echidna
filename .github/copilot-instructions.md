<!--
SPDX-License-Identifier: CC-BY-SA-4.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
<!-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk> -->
<!-- Authoritative source: docs/practice/AI-CONVENTIONS.adoc -->

# Copilot Instructions

## Before Writing Code

- Read `.machine_readable/descriptiles/` (STATE, META, ECOSYSTEM) for canonical
  file locations. echidna has not yet migrated these into a `*_chora.deed`.
- State files (.a2ml) live in `.machine_readable/` ONLY, never the root.

## License

- SPDX: `MPL-2.0` on all new files.
- Never use AGPL-3.0.
- Copyright: `Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>`

## Code Style

- Use descriptive variable names.
- Annotate and document all files.
- Add SPDX header to every source file.
- Use `just` for build/test/lint commands.

## Banned Patterns

- Idris2: no `believe_me`, no `assert_total`
- Haskell: no `unsafeCoerce`, no `unsafePerformIO`
- OCaml: no `Obj.magic`
- Coq: no `Admitted`
- Lean: no `sorry`
- Rust: no `transmute` unless FFI with `// SAFETY:` comment

## JavaScript / TypeScript runtimes

Ordered preference (`standards/3-practice/LANGUAGE-POLICY.adoc` §1) — reach for the first
that can do the job:

1. **Bun** — default for all new work. Runs compiled ESM/JS directly, no bundler
   step. Uses an npm-compatible `package.json` plus `bun.lock`; both are
   expected, not anti-patterns.
2. **pnpm** — only where an upstream toolchain requires `node_modules`.
3. **npm** — last resort. Permitted, never preferred; a deliberate, noted choice.

**Deno is being removed**, not grandfathered. Owner ruling 2026-08-26: *"deno is
to go and bun is the way we are going, put it first everywhere unless not
possible and explain why if not."* Existing Deno projects migrate to Bun; where
Bun genuinely cannot be used, document the reason in the repo.

**TypeScript is not the language for new application code — AffineScript is.**
`LANGUAGE-POLICY.adoc` §1.2, ruled 2026-08-25, separates two questions the older
text ran together: *runtime* is Bun (where `.ts` runs at all, Bun runs it), while
the *language* target is AffineScript. TypeScript is permitted only where
AffineScript cannot reach — the same narrow, transitional carve-out JavaScript
holds for MCP protocol glue and runtime APIs. ReScript remains banned; its
migration destination is AffineScript.

## Banned Languages

- No Go (use Rust)
- No Python (use Julia or Rust)
- No Nix (use Guix)
- No Deno for new work — being removed estate-wide; use Bun (owner ruling 2026-08-26)
- No ReScript (`LANGUAGE-POLICY.adoc` §3) — migrate to AffineScript

## Containers

- Use Podman, never Docker.
- Name the file `Containerfile`, never `Dockerfile`.
- Base image: `cgr.dev/chainguard/wolfi-base:latest`.

## ABI/FFI

- ABI definitions in Idris2 (`src/abi/`, package `src/abi/echidnaabi.ipkg`).
- FFI implementations in Zig (`ffi/zig/`, `src/zig_ffi/`).
- echidna keeps its own ABI/FFI layout rather than the template's interface tree.

## State Files

The retired STATE/META/ECOSYSTEM/AGENTIC/CLADE `.a2ml` files must not be
recreated anywhere; their content is in the repo deed (`*_chora.deed`) and
`docs/status/ROADMAP.adoc`.

Never create NEUROSYM.a2ml or PLAYBOOK.a2ml in the repo root.
They belong in `.machine_readable/` only.
