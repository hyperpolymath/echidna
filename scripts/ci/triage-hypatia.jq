# SPDX-License-Identifier: MPL-2.0
# Enrich Hypatia's findings without suppressing or changing their severity.
# Usage: jq --arg root "$PWD" -f scripts/ci/triage-hypatia.jq findings.json
# Use the ORIGINAL scan root for archived reports, not the current directory.

def member($items): . as $value | $items | index($value) != null;
def risk_class:
  if .rule_module == "migration_rules" then "language-migration"
  elif .rule_module != "code_safety" then "other"
  elif .type | member(["believe_me", "assert_total", "agda_postulate",
                       "lean_axiom", "lean_sorry", "coq_admitted", "coq_axiom",
                       "sorry", "admitted", "postulate", "unsafe_coerce"])
    then "proof-soundness"
  elif .type | member(["unsafe_block", "as_ptr", "zig_ptr_cast", "from_raw",
                       "mem_forget", "transmute", "raw_pointer_deref"])
    then "ffi-memory-safety"
  elif .type | member(["unwrap_without_check", "unwrap_dangerous_default",
                       "expect_in_hot_path", "panic_macro", "lock_unwrap"])
    then "runtime-availability"
  else "unclassified-code-safety" end;

def relative_file:
  (.file // "") as $path |
  ($root | rtrimstr("/")) as $prefix |
  if $prefix != "" and $path == $prefix then "."
  elif $prefix != "" and ($path | startswith($prefix + "/"))
    then $path | ltrimstr($prefix + "/")
  else $path | ltrimstr("./") end;

if type != "array" then error("expected a Hypatia findings array")
elif any(.[]; type != "object") then error("expected finding objects")
else map(
  risk_class as $risk | relative_file as $path |
  # Never infer test-only from a filename substring or a cfg(test) somewhere
  # in a mixed production module. Proof/FFI obligations retain expert review
  # even under tests/. Missing and unrecognised paths remain unreviewed.
  ($path | test("^(tests|benches|fuzz)/")) as $test_tree |
  . + {triage: {
    risk_class: $risk,
    source_file: $path,
    source_line: (.line // .start_line // null),
    context: (if $test_tree then "test-harness" else "production-or-unreviewed" end),
    priority: (if $test_tree and $risk == "runtime-availability"
               then "test-only-review" else "review" end),
    route: (if $risk == "proof-soundness" or $risk == "ffi-memory-safety"
            then "echidnabot"
            elif $risk == "runtime-availability" then "panicbot"
            elif $risk == "language-migration" then "rhodibot"
            else "manual-review" end),
    rationale: (if $test_tree and $risk == "runtime-availability"
                then "Non-deployed test/benchmark/fuzz harness; assertion-style failures may be intentional. Severity retained; review before suppression."
                elif $risk == "language-migration"
                then "Group by pattern and subtree; migration is not an independent security bug. Compile verification required before claiming a working port."
                elif $risk == "proof-soundness" or $risk == "ffi-memory-safety"
                then "Expert review required, including test fixtures. No automatic rewriting or default-value substitution."
                else "No suppression inferred. Inspect source context and preserve prover/error semantics." end)
  }}
) end
