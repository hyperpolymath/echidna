# ACL2 Example Proofs for ECHIDNA

This directory contains example ACL2 proofs demonstrating the ECHIDNA ACL2 backend capabilities.

## Files

### 1. `associativity.lisp`
Demonstrates associativity of a custom addition function with induction hints.

**Key Concepts:**
- Recursive function definition with `defun`
- Induction hints (`:hints (("Goal" :induct ...))`)
- Natural number reasoning with `natp`

### 2. `list_append.lisp`
Properties of list append operation.

**Theorems Proved:**
- `append-nil`: Appending nil is identity
- `append-associative`: Append is associative
- `length-append`: Length distributes over append

**Key Concepts:**
- List recursion with `endp`, `car`, `cdr`
- Multiple related theorems
- Structural induction

### 3. `factorial.lisp`
Factorial function with guards and tail-recursive variant.

**Theorems Proved:**
- `fact-positive`: Factorial is always positive
- `fact-tail-correct`: Tail-recursive version equivalence

**Key Concepts:**
- Guard verification with `declare xargs :guard`
- Type prescription rules (`:rule-classes :type-prescription`)
- Accumulator-based tail recursion

### 4. `binary_trees.lisp`
Binary tree operations and properties.

**Theorems Proved:**
- `mirror-involutive`: Mirror is its own inverse
- `mirror-preserves-size`: Mirror preserves tree size

**Key Concepts:**
- Data structure predicates (`tree-p`)
- Structural recursion on trees
- Property preservation proofs

### 5. `sorting.lisp`
Insertion sort correctness.

**Theorems Proved:**
- `insert-ordered`: Insert maintains sortedness
- `insertion-sort-ordered`: Insertion sort produces sorted output
- `member-insert`: Insert preserves membership

**Key Concepts:**
- Algorithm verification
- Conditional logic with `cond`
- Property-based specification (`ordered`)
- Using previous lemmas in proofs (`:use` hint)

## Running These Proofs

### With ACL2 Installed

```bash
# Interactive mode
acl2
ACL2 !> (ld "associativity.lisp")

# Batch mode
acl2 < associativity.lisp
```

### With ECHIDNA

```bash
# Parse and verify
echidna verify --prover acl2 associativity.lisp

# Interactive proof exploration
echidna repl --prover acl2
```

## ACL2 Syntax Cheat Sheet

### Function Definition
```lisp
(defun name (params)
  (if condition
      then-branch
    else-branch))
```

### Theorem Statement
```lisp
(defthm theorem-name
  (implies hypothesis
           conclusion)
  :hints (("Goal" :induct (function-name args))))
```

### Common Hints
- `:induct (f x)` - Induction on function application
- `:use lemma-name` - Use previously proved lemma
- `:expand (f x)` - Expand function definition
- `:in-theory (enable ...)` - Enable specific rules
- `:do-not-induct t` - Disable automatic induction

### Type Predicates
- `natp` - Natural number (≥ 0)
- `posp` - Positive integer (> 0)
- `integerp` - Integer
- `rationalp` - Rational number
- `true-listp` - Proper list

## Resources

- [ACL2 Documentation](http://www.cs.utexas.edu/users/moore/acl2/)
- [ACL2 Tutorial](http://www.cs.utexas.edu/users/moore/acl2/tutorial.html)
- [Proof Hints Guide](http://www.cs.utexas.edu/users/moore/acl2/current/manual/index.html?topic=ACL2____HINTS)
