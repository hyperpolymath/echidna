# HOL4 Example Proofs for ECHIDNA

This directory contains example HOL4 theories demonstrating the ECHIDNA HOL4 backend capabilities.

## Files

### 1. `list_append.sml`
List append properties with reverse.

**Theorems Proved:**
- `LENGTH_APPEND_THM`: Length distributes over append
- `APPEND_ASSOC_THM`: Append is associative
- `APPEND_NIL_RIGHT`: Nil is right identity
- `REVERSE_APPEND`: Reverse distributes over append
- `REVERSE_REVERSE`: Reverse is involutive

**Key Concepts:**
- List induction (`Induct`)
- Simplification (`rw[]`)
- Automated reasoning (`metis_tac`)
- Definition/Theorem forms

### 2. `arithmetic.sml`
Factorial, exponentiation, and sum formulas.

**Theorems Proved:**
- `FACT_POSITIVE`: Factorial is always positive
- `FACT_MONO`: Factorial is monotonic
- `EXP_ADD`: Exponent addition law
- `EXP_MULT`: Exponent multiplication law
- `SUM_TO_FORMULA`: Sum of first n naturals

**Key Concepts:**
- Recursive definitions
- Decision procedures (`DECIDE_TAC`)
- Arithmetic reasoning
- Induction over naturals

### 3. `binary_tree.sml`
Binary tree operations and properties.

**Theorems Proved:**
- `MIRROR_MIRROR`: Mirror is involutive
- `MIRROR_SIZE`: Mirror preserves size
- `MIRROR_HEIGHT`: Mirror preserves height
- `SIZE_INORDER`: Size equals inorder length
- `PERFECT_SIZE`: Perfect tree size formula

**Key Concepts:**
- Datatype definitions
- Structural induction
- Complex recursive functions
- Property preservation

### 4. `sorting.sml`
Insertion sort and quicksort correctness.

**Theorems Proved:**
- `INSERT_SORTED`: Insert maintains sortedness
- `ISORT_SORTED`: Insertion sort produces sorted output
- `ISORT_COUNT`: Insertion sort preserves element counts
- `QSORT_SORTED`: Quicksort produces sorted output

**Key Concepts:**
- Algorithm verification
- Termination measures
- Filter-based definitions
- Permutation reasoning

### 5. `set_theory.sml`
Set operations using HOL4's pred_setTheory.

**Theorems Proved:**
- De Morgan's laws (2 theorems)
- Distributivity laws (2 theorems)
- Subset properties (3 theorems)
- Powerset theorems (3 theorems)
- Cardinality theorems (2 theorems)

**Key Concepts:**
- Higher-order predicates
- Extension principle
- Finite set theory
- Built-in set libraries

## Running These Proofs

### With HOL4 Installed

```bash
# Interactive mode
Holmake
hol

# In HOL4 REPL:
- use "list_append.sml";

# Or batch compile:
Holmake
```

### With ECHIDNA

```bash
# Parse and verify
echidna verify --prover hol4 list_append.sml

# Interactive proof mode
echidna repl --prover hol4
```

## HOL4 Syntax Cheat Sheet

### Theory Structure
```sml
open HolKernel boolLib bossLib;

val _ = new_theory "theory_name";

(* Definitions and theorems *)

val _ = export_theory();
```

### Definition Forms
```sml
Definition NAME_DEF:
  (f base_case = result) /\
  (f (recursive_case x) = body)
End
```

### Theorem Form (New Style)
```sml
Theorem NAME:
  !x y. premise ==> conclusion
Proof
  tactic1 >>
  tactic2 >>
  ...
QED
```

### Theorem Form (Old Style)
```sml
val NAME = store_thm("NAME",
  ``!x y. premise ==> conclusion``,
  tactic1 >> tactic2 >> ...);
```

### Common Tactics
| Tactic | Purpose |
|--------|---------|
| `rw[]` | Rewrite with theorems |
| `simp[]` | Simplification |
| `fs[]` | Full simplification |
| `gs[]` | Goal simplification |
| `Induct` | List induction |
| `Induct_on 'var'` | Induction on variable |
| `Cases_on 'expr'` | Case split |
| `DECIDE_TAC` | Arithmetic decision |
| `ARITH_TAC` | Arithmetic automation |
| `metis_tac[]` | Automated reasoning |
| `irule thm` | Apply theorem backwards |
| `EVAL_TAC` | Computation |

### Tactic Combinators
| Combinator | Meaning |
|------------|---------|
| `t1 >> t2` | Sequence (then) |
| `t1 ORELSE t2` | Try t1, else t2 |
| `REPEAT t` | Repeat until fails |
| `TRY t` | Try t, don't fail |
| `ALL_TAC` | Do nothing |

### Datatype Definition
```sml
Datatype:
  tree = Leaf
       | Node tree 'a tree
End
```

## Proof Style Guidelines

### Goal-Oriented Style
```sml
Proof
  Induct >> rw[] >>
  Cases_on 'l' >> fs[] >>
  metis_tac[LEMMA_NAME]
QED
```

### Named Intermediate Steps
```sml
Proof
  rw[] >>
  'intermediate_fact' by (simp[] >> DECIDE_TAC) >>
  'another_fact' by metis_tac[LEMMA] >>
  DECIDE_TAC
QED
```

## Resources

- [HOL4 Website](https://hol-theorem-prover.org/)
- [HOL4 Tutorial](https://sourceforge.net/projects/hol/files/hol/kananaskis-14/)
- [HOL4 Description Manual](https://hol-theorem-prover.org/kananaskis-14-helpdocs/help/Docfiles/HTML/Description.html)
- [HOL4 Tactic Reference](https://hol-theorem-prover.org/kananaskis-14-helpdocs/help/Docfiles/HTML/tactic_index.html)
- [bossLib Automation](https://hol-theorem-prover.org/kananaskis-14-helpdocs/help/Docfiles/HTML/bossLib.html)
