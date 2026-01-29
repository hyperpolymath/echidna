# ECHIDNA Example Proofs

This directory contains example proofs demonstrating ECHIDNA's capabilities across all 12 supported provers.

## Quick Try

### Coq Example (simple_proof.v)

```bash
# Start ECHIDNA
./start.sh

# In the UI:
# 1. Select "Coq" prover
# 2. Load examples/simple_proof.v
# 3. Use tactic suggester to get AI recommendations
```

### Via API

```bash
# Verify the proof via API
curl -X POST http://127.0.0.1:8080/api/verify \
  -H "Content-Type: application/json" \
  -d @- << JSON
{
  "prover": "Coq",
  "content": "$(cat simple_proof.v)"
}
JSON
```

## Available Examples

| File | Prover | Description |
|------|--------|-------------|
| `simple_proof.v` | Coq | Basic arithmetic proofs |
| `(more coming)` | Various | Additional examples |

## Learning Path

1. **Start Simple**: Try `simple_proof.v` to understand basic workflow
2. **Explore Tactics**: Use the AI suggester to discover new tactics
3. **Filter by Aspect**: Try different aspect tags to see specialized suggestions
4. **Visualize**: Watch the proof tree grow as you build your proof
5. **Compare Provers**: Try the same theorem in different provers

## Tips

- Use aspect tags to filter suggestions:
  - `algebraic` - For algebraic properties
  - `geometric` - For geometric reasoning
  - `logical` - For logical inferences
  - `inductive` - For induction-based proofs
  - `deductive` - For direct reasoning
  - `automated` - For automatic tactics

- Check confidence scores - higher confidence (>0.8) suggestions are more likely to succeed

- Explore the proof tree to understand proof structure

## Adding Your Own Examples

To add new examples:

1. Create a file with appropriate extension (`.v`, `.lean`, `.thy`, etc.)
2. Add SPDX header for licensing
3. Include comments explaining the proof
4. Test it works with ECHIDNA
5. Submit a PR!

---

**Happy Proving! 🦔**
