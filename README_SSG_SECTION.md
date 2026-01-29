<!-- 
SPDX-License-Identifier: PMPL-1.0-or-later-or-later
SPDX-FileCopyrightText: 2024-2025 ECHIDNA Project Contributors

Insert this section into README.adoc after the "## Features" section
-->

## Static Site Generation Integration

ECHIDNA's verification capabilities extend to static site generation through three active development tracks:

### `echidna-docs` — Proof Content SSG 🟢

Static site generator that understands formal proof content from all 12 supported theorem provers.

```bash
echidna-docs build --source proofs/ --output site/
```

**Features:**
- Semantic syntax highlighting (type-aware, not regex-based)
- Proof dependency graph generation
- Aspect-tagged navigation (algebraic, topological, combinatorial, etc.)
- Cross-prover theorem linking
- Interactive proof stepping (where supported)

**Status:** Active development — Agda/Lean/Coq parsers complete, renderer in progress.

### `echidna-verify` — Property Oracle MCP 🟡

MCP server for verifying semantic properties of SSG implementations. Integrates with [polyglot-ssg-mcp](https://github.com/hyperpolymath/polyglot-ssg-mcp) to ensure semantic equivalence across implementations in different languages.

**MCP Tools:**
- `verify_ssg_property` — Verify properties like HTML well-formedness, rendering idempotence
- `compare_implementations` — Check two SSG implementations produce equivalent output
- `generate_counterexample` — Find inputs that distinguish differing implementations

**Status:** Architecture complete, solver integration done, property encoders in progress.

### `libechidna-ssg` — Verified Core Library 🔵

Formally verified SSG core with proofs in Agda, extracted to a shared native library with FFI bindings for multiple languages.

**Properties under formal verification:**
1. Rendering idempotence: `render(render(x)) = render(x)`
2. Structure preservation: Document structure maintained across transformations
3. HTML well-formedness: Output always valid HTML5
4. Template safety: No injection through template variables
5. Determinism: Same input → same output

**Status:** Specification phase — Agda AST module and property sketches in progress.

See [SSG_ROADMAP.adoc](SSG_ROADMAP.adoc) for detailed timeline and architecture.
