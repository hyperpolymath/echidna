# echidna-mcp

Model Context Protocol server that exposes [ECHIDNA](https://github.com/hyperpolymath/echidna)'s
105-prover portfolio to AI coding agents (Claude Code, Claude API, etc.) as first-class
tool-use actions over stdio.

## Installation

```sh
# From source (workspace root)
cargo install --path crates/echidna-mcp

# Or build without installing
cargo build -p echidna-mcp --release
```

The `echidna` binary must be on `PATH` (or set `ECHIDNA_BIN=/abs/path/echidna`).

## Claude Code integration

Add to your project's `.claude/settings.json`:

```json
{
  "mcpServers": {
    "echidna": {
      "command": "echidna-mcp"
    }
  }
}
```

Or with an explicit binary path:

```json
{
  "mcpServers": {
    "echidna": {
      "command": "echidna-mcp",
      "env": { "ECHIDNA_BIN": "/usr/local/bin/echidna" }
    }
  }
}
```

## Tools

### `prove`

Prove a theorem from a file using one of ECHIDNA's 105 backends.

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `file` | string | yes | Absolute path to the proof file |
| `prover` | string | no | Backend name (e.g. `Z3`, `Coq`, `Lean`, `Isabelle`). Auto-detected from extension if omitted. |
| `timeout_secs` | integer | no | Prover timeout in seconds. Default: 300. |

**Returns** a JSON object:
```json
{
  "verified": true,
  "message": "Goal discharged.",
  "prover": "Z3",
  "raw_output": "...",
  "stderr": ""
}
```

**Accepted file formats** (by prover):

| Extension | Prover |
|-----------|--------|
| `.smt2` | Z3, CVC5, Alt-Ergo |
| `.lean` | Lean 4 |
| `.v` | Coq / Rocq |
| `.agda` | Agda |
| `.thy` | Isabelle/HOL |
| `.miz` | Mizar |
| `.fst` | F* |
| `.dfg` | SPASS |
| `.mm` | Metamath |

## Example JSON-RPC exchanges

### Prove a trivial SMT goal with Z3

Request:
```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "method": "tools/call",
  "params": {
    "name": "prove",
    "arguments": {
      "file": "/tmp/reflexivity.smt2",
      "prover": "Z3",
      "timeout_secs": 10
    }
  }
}
```

`/tmp/reflexivity.smt2`:
```smt2
(declare-const x Int)
(assert (not (= x x)))
(check-sat)
```

Response:
```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "result": {
    "content": [{
      "type": "text",
      "text": "{\n  \"verified\": true,\n  \"message\": \"unsat\",\n  \"prover\": \"Z3\",\n  \"raw_output\": \"unsat\\n\",\n  \"stderr\": \"\"\n}"
    }]
  }
}
```

### Auto-detect prover from extension

```json
{
  "jsonrpc": "2.0",
  "id": 2,
  "method": "tools/call",
  "params": {
    "name": "prove",
    "arguments": {
      "file": "/workspace/lemmas/associativity.v"
    }
  }
}
```

ECHIDNA detects `.v` → Coq and routes accordingly.

## Troubleshooting

**`Failed to invoke echidna: No such file or directory`**
: The `echidna` binary is not on PATH. Either install it or set `ECHIDNA_BIN=/full/path/echidna` in the MCP server env config.

**`verified: false` with empty `message`**
: The prover binary itself is missing. Confirm the target prover is installed: `which z3`, `which coqc`, etc. The `echidna check-prover <Name>` command also reports availability.

**Timeout / `verified: false` with partial output**
: Increase `timeout_secs`. Complex goals in interactive provers (Isabelle, Coq) may need 60–600 s. Default is 300 s.

**Wrong prover selected**
: Pass `"prover": "Z3"` (or whichever backend) explicitly rather than relying on auto-detection.

## License

PMPL-1.0-or-later — see [LICENSE](../../LICENSE).
