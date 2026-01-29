# PVS Example Proofs for ECHIDNA

This directory contains example PVS specifications demonstrating the ECHIDNA PVS backend capabilities.

## Files

### 1. `list_theory.pvs`
Parametric list theory with append and length.

**Theorems Proved:**
- `append_nil_right`: Appending empty list is identity
- `append_associative`: Append is associative
- `length_append`: Length distributes over append

**Key Concepts:**
- Parametric theories (`[T: TYPE]`)
- Datatype definitions
- Recursive functions with MEASURE clauses
- CASES expressions

### 2. `arithmetic.pvs`
Arithmetic properties and recursive functions.

**Theorems Proved:**
- Basic arithmetic properties (commutativity, associativity, distributivity)
- `factorial_positive`: Factorial is always positive
- `factorial_increasing`: Factorial is monotonic
- `fib_positive`: Fibonacci numbers are positive

**Key Concepts:**
- Natural number arithmetic
- RECURSIVE functions with MEASURE
- IF-THEN-ELSE vs CASES
- Dependent types with TCCs

### 3. `binary_search.pvs`
Binary search algorithm specification and correctness.

**Theorems Proved:**
- `binary_search_correct`: Algorithm finds element if present

**Key Concepts:**
- Array theory (IMPORTING arrays@array_ops)
- Preconditions with sorted?
- LET bindings
- Postconditions with implications
- Algorithm verification

### 4. `set_theory.pvs`
Set operations using higher-order predicates.

**Theorems Proved:**
- De Morgan's laws (2 theorems)
- Set algebra (commutativity, associativity)
- Subset properties (reflexive, transitive)

**Key Concepts:**
- Higher-order types (`set: TYPE = [T -> bool]`)
- Lambda expressions
- First-class predicates
- Extensionality

### 5. `sorting.pvs`
Insertion sort with correctness and permutation preservation.

**Theorems Proved:**
- `insert_sorted`: Insert maintains sortedness
- `insertion_sort_sorted`: Sort produces sorted output
- `insert_preserves_occurrences`: Permutation preservation

**Key Concepts:**
- Parametric theory with ordering relation
- total_order? predicate
- Algorithm correctness
- Counting occurrences
- Property preservation

## Running These Proofs

### With PVS Installed

```bash
# Start PVS Emacs interface
pvs

# Or use command-line
pvs -batch -l list_theory.pvs

# Type check theory
M-x typecheck-file

# Prove theorem
M-x prove
```

### With ECHIDNA

```bash
# Parse and verify
echidna verify --prover pvs list_theory.pvs

# Check type correctness conditions (TCCs)
echidna check-tccs --prover pvs arithmetic.pvs
```

## PVS Syntax Cheat Sheet

### Theory Structure
```pvs
theory_name: THEORY
BEGIN
  % Definitions and theorems
END theory_name
```

### Parametric Theory
```pvs
theory_name[T: TYPE, R: (relation?[T])]: THEORY
BEGIN
  ...
END theory_name
```

### Function Definition
```pvs
function_name(x: type1, y: type2): RECURSIVE return_type =
  body
MEASURE measure_expression
```

### Theorem Statement
```pvs
theorem_name: THEOREM
  FORALL (x: type): precondition IMPLIES conclusion
```

### Common Proof Commands
- `(grind)` - Powerful automated proof
- `(split)` - Case split
- `(induct "var")` - Induction
- `(expand "function")` - Expand definition
- `(lemma "name")` - Apply lemma
- `(skolem!)` - Skolemize quantifiers

### Type Checking
- TCCs (Type Correctness Conditions) auto-generated for:
  - Array bounds
  - Division by zero
  - Recursive function termination
  - Subtype constraints

## Resources

- [PVS Specification and Verification System](http://pvs.csl.sri.com/)
- [PVS Language Reference](http://pvs.csl.sri.com/doc/pvs-language-reference.pdf)
- [PVS Prover Guide](http://pvs.csl.sri.com/doc/pvs-prover-guide.pdf)
- [PVS Tutorial](http://shemesh.larc.nasa.gov/fm/pvs/tutorial/)
