## Machine-Readable Artefacts

The following files in `.machine_readable/` contain structured project metadata:

- `.machine_readable/6a2/STATE.a2ml` - Current project state and progress
- `.machine_readable/6a2/META.a2ml` - Architecture decisions and development practices
- `.machine_readable/6a2/ECOSYSTEM.a2ml` - Position in the ecosystem and related projects
- `.machine_readable/6a2/AGENTIC.a2ml` - AI agent interaction patterns
- `.machine_readable/6a2/NEUROSYM.a2ml` - Neurosymbolic integration config
- `.machine_readable/6a2/PLAYBOOK.a2ml` - Operational runbook
- `.machine_readable/bot_directives/*.a2ml` - Per-bot permission and scope rules

## Canonical Roadmap

See [`docs/ROADMAP.md`](../docs/ROADMAP.md) for the single source of truth on
where ECHIDNA is going: the 8‑stage map, row‑by‑row endpoint targets,
current sprint (S1–S5), and agent‑tier guidance.  Record decisions
there, not in chat.

## Supervised Multi-Agent Execution

When a supervising agent (Opus) plans work that will be implemented by
a focused executor (Sonnet) or a mechanical bulk agent (Haiku), the
supervisor MUST run a **Haiku scout pass** immediately before spawning
the implementation agent, unless the scope is strictly single‑file
and under ten lines of change.

### Scout pattern

**Purpose**: clear obvious cruft (unused imports, stale comments,
dead stubs, broken references) so the implementation agent arrives
to clean ground and does not burn tokens on trivial lint.

**When to run**: once per upcoming step, after the step's scope is
locked and before the implementation agent is launched.

**Prompt template** (copy this verbatim, fill in the file list):

```
Haiku scout, scope = <exact file list for the step>

1. Confirm each file compiles in isolation (cargo check --lib / julia -e).
2. Scan for: unused imports, dead code, `todo!()/FIXME/XXX`,
   orphan type references, stale doc comments referring to
   renamed symbols, broken `mod.rs` exports.
3. Trivially fix:
   - unused imports (remove)
   - obvious typos in comments
   - unused `_var` renames
4. DO NOT fix — FLAG to me:
   - any TODO with semantic content (may be load-bearing)
   - anything requiring judgement about intent
   - any cross-module change
5. Report: <20 lines. Green-light or list of blockers.
```

**Caveats**:

- Scout is **not** a full audit.  Full audits remain the periodic
  cross‑module sweep (cf. the Agent A + Agent B pattern in session
  history); scout is narrow prep for an imminent step.
- Scout must **not over‑fix**.  TODO/FIXME comments sometimes
  contain the spec for the upcoming work — flag, don't delete.
- Scout is **idempotent**.  Re‑running on unchanged code should
  produce the same report.
- If scout flags a blocker, the supervisor decides whether to
  resolve it inline, expand the step's scope, or defer.  The
  implementation agent does not launch until the supervisor
  green‑lights.

**Commit convention** (when the scout applied trivial fixes):

```
chore(<scope>): scout-pass trivial cleanup ahead of <step id>
```

### CRITICAL: .scm metadata files are DEPRECATED

**All `.scm` state/metadata files have been replaced by `.a2ml`.**

If you find any `.scm` file under `.machine_readable/` (e.g. `STATE.scm`, `META.scm`,
`ECOSYSTEM.scm`, `AGENTIC.scm`, `NEUROSYM.scm`, `PLAYBOOK.scm`, bot directive `.scm`
files, or similar), you MUST:

1. Check whether an equivalent `.a2ml` file already exists
2. If yes — delete the `.scm` file immediately (`git rm`)
3. If no — convert its content to A2ML format first, then delete the `.scm` original

**Exception:** `guix.scm` files and files under `guix/` or `guix-channel/` are Guix
package definitions (not metadata files) and must NOT be deleted.

---

# CLAUDE.md - AI Assistant Instructions

## Language Policy (Hyperpolymath Standard)

### ALLOWED Languages & Tools

| Language/Tool | Use Case | Notes |
|---------------|----------|-------|
| **ReScript** | Primary application code | Compiles to JS, type-safe |
| **Deno** | Runtime & package management | Replaces Node/npm/bun |
| **Rust** | Performance-critical, systems, WASM | Preferred for CLI tools |
| **Tauri 2.0+** | Mobile apps (iOS/Android) | Rust backend + web UI |
| **Dioxus** | Mobile apps (native UI) | Pure Rust, React-like |
| **Gleam** | Backend services | Runs on BEAM or compiles to JS |
| **Bash/POSIX Shell** | Scripts, automation | Keep minimal |
| **JavaScript** | Only where ReScript cannot | MCP protocol glue, Deno APIs |
| **Nickel** | Configuration language | For complex configs |
| **Guile Scheme** | State/meta files | .machine_readable/6a2/STATE.a2ml, .machine_readable/6a2/META.a2ml, .machine_readable/6a2/ECOSYSTEM.a2ml |
| **Julia** | Batch scripts, data processing | Per RSR |
| **OCaml** | AffineScript compiler | Language-specific |
| **Ada** | Safety-critical systems | Where required |

### BANNED - Do Not Use

| Banned | Replacement |
|--------|-------------|
| TypeScript | ReScript |
| Node.js | Deno |
| npm | Deno |
| Bun | Deno |
| pnpm/yarn | Deno |
| Go | Rust |
| Python | Julia/Rust/ReScript |
| Java/Kotlin | Rust/Tauri/Dioxus |
| Swift | Tauri/Dioxus |
| React Native | Tauri/Dioxus |
| Flutter/Dart | Tauri/Dioxus |

### Mobile Development

**No exceptions for Kotlin/Swift** - use Rust-first approach:

1. **Tauri 2.0+** - Web UI (ReScript) + Rust backend, MIT/Apache-2.0
2. **Dioxus** - Pure Rust native UI, MIT/Apache-2.0

Both are FOSS with independent governance (no Big Tech).

### Enforcement Rules

1. **No new TypeScript files** - Convert existing TS to ReScript
2. **No package.json for runtime deps** - Use deno.json imports
3. **No node_modules in production** - Deno caches deps automatically
4. **No Go code** - Use Rust instead
5. **No Python anywhere** - Use Julia for data/batch, Rust for systems, ReScript for apps
6. **No Kotlin/Swift for mobile** - Use Tauri 2.0+ or Dioxus

### Package Management

- **Primary**: Guix (guix.scm)
- **Fallback**: Nix (flake.nix)
- **JS deps**: Deno (deno.json imports)

### Security Requirements

- No MD5/SHA1 for security (use SHA256+)
- HTTPS only (no HTTP URLs)
- No hardcoded secrets
- SHA-pinned dependencies
- SPDX license headers on all files

