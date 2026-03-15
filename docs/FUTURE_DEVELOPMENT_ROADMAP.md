# ECHIDNA Future Development Roadmap

**Status**: Vision Document
**Date**: 2026-01-29
**Purpose**: Extended development ideas beyond current implementation

---

## Overview

This document outlines advanced features and research directions that could take ECHIDNA from a powerful neurosymbolic prover to a **world-class automated reasoning system**.

---

## 1. Advanced ML Integration

### 1.1 Reinforcement Learning for Tactic Search

**Current**: Logistic regression suggests tactics based on bag-of-words

**Future**: RL agent learns optimal tactic sequences from experience

**Implementation**:
```julia
# src/julia/rl_tactic_agent.jl
using ReinforcementLearning
using Flux

struct ProofEnvironment <: AbstractEnv
    state::ProofState
    goal::String
    max_steps::Int
end

# State = proof state embedding (GNN)
# Action = tactic to apply
# Reward = progress toward goal (+ bonus for completion)

agent = Agent(
    policy = QBasedPolicy(
        learner = DQNLearner(
            approximator = NeuralNetworkApproximator(
                model = Chain(
                    Dense(256, 128, relu),
                    Dense(128, num_tactics)
                )
            )
        )
    )
)

# Train on successful proofs
for proof in training_corpus
    run(agent, ProofEnvironment(proof.goal))
end
```

**Benefits**:
- Learns from mistakes (failed tactics penalized)
- Discovers novel tactic sequences
- Generalizes beyond training theorems
- Continuous improvement over time

**Challenges**:
- Large state space (proof states complex)
- Sparse rewards (most steps don't complete proof)
- Need simulator (fast prover mock)

**Timeline**: 3-6 months research, 2-3 months implementation

---

### 1.2 Graph Neural Networks for Proof States

**Current**: Text-based bag-of-words encoding

**Future**: Structured graph representation of proof state

**Why Graphs?**
- Proofs are **trees** (natural graph structure)
- Premises have **dependencies** (edges)
- GNNs preserve **relational structure**

**Architecture**:
```python
# Conceptual (would be Julia/Rust)
class ProofStateGNN(nn.Module):
    def __init__(self):
        self.node_encoder = GCNConv(feature_dim, 128)
        self.graph_pooling = GlobalAttentionPooling()
        self.tactic_head = Linear(128, num_tactics)

    def forward(self, proof_graph):
        # Nodes = terms, hypotheses, goals
        # Edges = dependencies, type relations
        x = self.node_encoder(proof_graph)
        x = self.graph_pooling(x)
        return self.tactic_head(x)
```

**Benefits**:
- Captures proof structure
- Better generalization
- Handles complex premises

**Timeline**: 4-6 months (research-heavy)

---

### 1.3 Transformer-Based Premise Selection

**Current**: Simple vocabulary matching

**Future**: Semantic similarity via transformers (like BERT for proofs)

**Model**: ProofBERT
```julia
# src/julia/premise_transformer.jl
using Transformers

# Pre-trained on 100K+ proofs
model = load_transformer("ProofBERT-base")

# Encode goal
goal_embedding = model.encode("forall n m, n + m = m + n")

# Find relevant premises by cosine similarity
premise_embeddings = model.encode.(premise_library)
similarities = cosine_similarity.(Ref(goal_embedding), premise_embeddings)

# Top-K relevant premises
top_premises = premise_library[sortperm(similarities, rev=true)[1:5]]
```

**Benefits**:
- Semantic understanding (not just keyword matching)
- Finds non-obvious relevant lemmas
- Transfer learning from math corpus

**Data Sources**:
- Coq standard library (30K+ lemmas)
- Lean Mathlib (100K+ theorems)
- Isabelle AFP (3M+ lines)
- arXiv math papers (1M+ documents)

**Timeline**: 6-12 months (requires large-scale training)

---

### 1.4 Active Learning & Human Feedback

**Concept**: Ask humans when uncertain

**Workflow**:
1. Prover attempts theorem
2. If stuck (no tactic > 50% confidence), ask human
3. Human provides hint or full tactic
4. Model learns from feedback
5. Improves for similar theorems

**UI**:
```
┌──────────────────────────────────────────┐
│ 🤔 ECHIDNA needs help!                   │
├──────────────────────────────────────────┤
│ Goal: ∀n m : ℕ, (n + m) * 2 = n*2 + m*2 │
│                                          │
│ Current state:                           │
│   Hypotheses: n m : ℕ                    │
│   Goal: (n + m) * 2 = n*2 + m*2          │
│                                          │
│ Best suggestions (all < 50%):            │
│   • intro (42%)                          │
│   • simpl (38%)                          │
│   • ring (35%)                           │
│                                          │
│ What tactic should I try?                │
│ ┌────────────────────────────────────┐   │
│ │ ring                               │   │
│ └────────────────────────────────────┘   │
│          [Submit]   [Skip]               │
└──────────────────────────────────────────┘
```

**Benefits**:
- Learns from experts
- Handles edge cases
- Continuous improvement

**Timeline**: 2-3 months

---

## 2. Proof Repair & Synthesis

### 2.1 Automatic Proof Repair

**Problem**: Library update breaks 1000 proofs

**Solution**: Auto-repair changed APIs

**Example**:
```coq
(* Old: List.app deprecated *)
Lemma old_proof : forall l1 l2,
  List.app l1 l2 = l1 ++ l2.

(* New: List.app → List.append *)
Lemma repaired_proof : forall l1 l2,
  List.append l1 l2 = l1 ++ l2.
```

**Algorithm**:
1. Detect failure reason (undefined `List.app`)
2. Search for replacement (`List.append`)
3. Try substitution
4. Verify repair works

**Implementation**:
```rust
// src/rust/proof_repair.rs
pub struct ProofRepairer {
    api_migrations: HashMap<String, String>,
    tactic_rewrites: Vec<RewriteRule>,
}

impl ProofRepairer {
    pub fn repair(&self, broken_proof: &Proof) -> Result<Proof> {
        // 1. Parse error message
        let error = broken_proof.error()?;

        // 2. Identify cause
        let cause = self.diagnose(&error)?;

        // 3. Apply fix
        match cause {
            BreakageCause::DeprecatedAPI(old) => {
                let new = self.api_migrations.get(&old)?;
                broken_proof.replace_symbol(&old, &new)
            }
            BreakageCause::ChangedTactic(tactic) => {
                let rewrite = self.find_rewrite(&tactic)?;
                broken_proof.apply_rewrite(&rewrite)
            }
        }
    }
}
```

**Timeline**: 3-4 months

---

### 2.2 Proof Minimization

**Problem**: Proof has 50 tactics, but 5 would suffice

**Goal**: Find shortest equivalent proof

**Approach**: Delta debugging
```rust
fn minimize_proof(proof: &Proof) -> Proof {
    let mut tactics = proof.tactics.clone();

    for i in 0..tactics.len() {
        // Try removing tactic i
        let candidate = remove(&tactics, i);

        if verify(&candidate).is_ok() {
            tactics = candidate; // Removal succeeded
        }
    }

    Proof { tactics }
}
```

**Benefits**:
- Easier to understand
- Faster to check
- Better for teaching

**Timeline**: 1-2 months

---

### 2.3 Counterexample Generation

**Problem**: Theorem unprovable, but why?

**Solution**: Generate counterexample showing it's false

**Example**:
```
Goal: ∀n : ℕ, n * 0 = 1
ECHIDNA: ✗ Unprovable

Counterexample: n = 5
  5 * 0 = 0 ≠ 1
```

**Implementation** (via SMT solver):
```rust
fn find_counterexample(goal: &Term) -> Option<Valuation> {
    let negation = negate(goal);
    let solver = Z3Solver::new();

    solver.assert(negation);

    match solver.check() {
        Sat => Some(solver.get_model()),
        Unsat => None, // Goal is valid (no counterexample)
        Unknown => None,
    }
}
```

**Timeline**: 2-3 months

---

## 3. Distributed & Cloud Infrastructure

### 3.1 Distributed Proof Search

**Current**: 12 provers on one machine (Chapel parallelism)

**Future**: 1000 provers across cluster

**Architecture**:
```
┌──────────────┐
│  Coordinator │  (Rust + Chapel)
└──────┬───────┘
       │
   ┌───┴────────┬────────┬────────┐
   │            │        │        │
┌──▼──┐     ┌──▼──┐  ┌──▼──┐  ┌──▼──┐
│Node1│     │Node2│  │Node3│  │Node4│
│Coq  │     │Lean │  │Agda │  │Z3   │
│Lean │     │Coq  │  │Lean │  │CVC5 │
│Agda │     │Agda │  │Coq  │  │Lean │
└─────┘     └─────┘  └─────┘  └─────┘
```

**Chapel's PGAS (Partitioned Global Address Space)**:
```chapel
// Distribute provers across locales (machines)
config const numNodes = 4;

coforall loc in Locales {
  on loc {
    // Each machine runs subset of provers
    var local_provers = get_provers_for_locale(loc.id);

    coforall prover in local_provers {
      var result = tryProve(prover, goal);
      if result.success {
        broadcast_success(result); // Notify all nodes
      }
    }
  }
}
```

**Benefits**:
- Scale to 100+ concurrent provers
- Geographic distribution (low latency worldwide)
- Fault tolerance (node failure doesn't stop search)

**Timeline**: 3-6 months

---

### 3.2 Cloud Integration

**Deployment Options**:

**AWS Lambda** (serverless):
```rust
// lambda/prove_handler.rs
use lambda_runtime::{handler_fn, Context, Error};

#[tokio::main]
async fn main() -> Result<(), Error> {
    let handler = handler_fn(prove_handler);
    lambda_runtime::run(handler).await?;
    Ok(())
}

async fn prove_handler(
    event: ProofRequest,
    _: Context
) -> Result<ProofResponse, Error> {
    // Spin up prover (cold start ~100ms)
    let result = echidna::prove(&event.goal).await?;
    Ok(result)
}
```

**Google Cloud Functions**:
```julia
# cloud_function/main.jl
using GoogleCloud

function prove_theorem(request::HTTP.Request)
    goal = JSON3.read(request.body).goal
    result = ECHIDNA.prove(goal)

    return HTTP.Response(200, JSON3.write(result))
end

GoogleCloud.deploy("echidna-prove", prove_theorem)
```

**Benefits**:
- Auto-scaling (0 → 1000 instances)
- Pay-per-use (no idle costs)
- Global CDN distribution

**Timeline**: 2-3 months

---

### 3.3 Proof Caching (Distributed Redis)

**Problem**: Same lemmas proven repeatedly

**Solution**: Shared proof cache

```rust
// src/rust/proof_cache.rs
use redis::AsyncCommands;

pub struct ProofCache {
    redis: redis::Client,
}

impl ProofCache {
    pub async fn get(&self, goal: &str) -> Option<Proof> {
        let mut conn = self.redis.get_async_connection().await.ok()?;
        let cached: Option<String> = conn.get(goal).await.ok()?;
        cached.and_then(|s| serde_json::from_str(&s).ok())
    }

    pub async fn set(&self, goal: &str, proof: &Proof) {
        let mut conn = self.redis.get_async_connection().await.unwrap();
        let serialized = serde_json::to_string(proof).unwrap();
        let _: () = conn.set_ex(goal, serialized, 86400).await.unwrap(); // 24h TTL
    }
}
```

**Benefits**:
- Instant results for common lemmas
- Shared across all users
- TTL prevents stale proofs

**Timeline**: 1-2 months

---

## 4. User Experience Enhancements

### 4.1 Visual Proof Editor

**Inspiration**: Lean 4 VS Code extension, Coq IDE

**Features**:
- **Syntax highlighting** for all 12 provers
- **Inline goals** (see goal state at cursor)
- **Autocomplete** (tactic suggestions as you type)
- **Error highlighting** (red squiggles for invalid tactics)
- **Proof tree visualization** (interactive graph)

**Mock UI**:
```
┌─────────────────────────────────────────────────────────┐
│ File  Edit  View  Proof  Help                          │
├─────────────────────────────────────────────────────────┤
│  1  Theorem add_comm : forall n m : nat,               │
│  2    n + m = m + n.                                    │
│  3  Proof.                                              │
│  4    intros n m.          │ Goal: n + m = m + n       │
│  5    induction n as [|n']. │                           │
│  6    - simpl. reflexivity. │ ✓ Subgoal 1 complete     │
│  7    - simpl.              │ Goal: S n' + m = m + S n'│
│  8      rewrite IHn'.       │ ← [AI suggests: rewrite] │
│  9      rewrite plus_n_Sm.  │                           │
│ 10      reflexivity.        │ ✓ Proof complete         │
│ 11  Qed.                                                │
└─────────────────────────────────────────────────────────┘
```

**Implementation**: Dioxus desktop app or VS Code extension

**Timeline**: 6-9 months

---

### 4.2 Natural Language Proof Explanation

**Problem**: Proof is valid but incomprehensible

**Solution**: Generate English explanation

**Example**:
```
Input (Coq):
  intros n m.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.

Output (English):
  To prove that n + m = m + n for all natural numbers n and m:

  1. Introduce variables n and m.
  2. Proceed by induction on n.
  3. Base case (n = 0):
     - Simplify both sides (0 + m = m + 0).
     - Both sides are equal by reflexivity.
  4. Inductive case (n = S n'):
     - Simplify to get S(n' + m) = m + S(n').
     - Apply the inductive hypothesis (n' + m = m + n').
     - Both sides are now equal.
  5. Therefore, the theorem holds for all n and m.
```

**Implementation**: Fine-tuned LLM
```python
# Train on (proof, explanation) pairs
model = T5ForConditionalGeneration.from_pretrained("t5-large")
tokenizer = T5Tokenizer.from_pretrained("t5-large")

# Fine-tune on proof corpus
train_data = [
    ("intros. reflexivity.", "Introduce variables and apply reflexivity."),
    ("induction n.", "Proceed by induction on n."),
    # ... 10K examples
]

# Generate explanation
input_ids = tokenizer(proof_text, return_tensors="pt").input_ids
output = model.generate(input_ids, max_length=200)
explanation = tokenizer.decode(output[0])
```

**Timeline**: 4-6 months (requires training corpus)

---

### 4.3 Interactive Learning Mode

**Target Audience**: Students learning theorem proving

**Features**:
- **Guided proofs** (step-by-step with hints)
- **Exercises** (graded difficulty)
- **Feedback** ("Good! Now try cases on m")
- **Achievements** (gamification)

**Example Session**:
```
┌──────────────────────────────────────────────────────┐
│ 📚 ECHIDNA Learning Mode                            │
│                                                      │
│ Lesson 3: Induction Proofs                          │
│ ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ │
│                                                      │
│ Exercise: Prove that ∀n : ℕ, n + 0 = n             │
│                                                      │
│ Current state:                                       │
│   Goal: ∀n : ℕ, n + 0 = n                           │
│                                                      │
│ Your tactic: ▓                                       │
│                                                      │
│ 💡 Hint: When you see ∀, try introducing the        │
│          variable first.                             │
│                                                      │
│ Progress: ██░░░░░░░░ 2/10 exercises                 │
└──────────────────────────────────────────────────────┘
```

**Timeline**: 3-4 months

---

## 5. Formal Methods Integration

### 5.1 SMT-LIB 2.0 Export

**Why**: Standard format for SMT solvers

**Example**:
```smt2
; Export ECHIDNA proof to SMT-LIB
(set-logic QF_NIA) ; Quantifier-free nonlinear integer arithmetic
(declare-fun n () Int)
(declare-fun m () Int)
(assert (= (+ n m) (+ m n))) ; Goal: n + m = m + n
(check-sat) ; Should return 'sat'
(get-model)
```

**Implementation**:
```rust
// src/rust/export/smtlib.rs
pub fn export_to_smtlib(proof: &Proof) -> String {
    let mut output = String::new();

    // Logic declaration
    output.push_str("(set-logic QF_NIA)\n");

    // Variable declarations
    for var in &proof.variables {
        output.push_str(&format!("(declare-fun {} () Int)\n", var));
    }

    // Assertions (premises)
    for premise in &proof.premises {
        output.push_str(&format!("(assert {})\n", to_smtlib(premise)));
    }

    // Goal
    output.push_str(&format!("(assert {})\n", to_smtlib(&proof.goal)));
    output.push_str("(check-sat)\n");

    output
}
```

**Benefits**:
- Interop with Z3, CVC4, etc.
- Benchmark suite integration
- Tool ecosystem access

**Timeline**: 2-3 months

---

### 5.2 TPTP Integration

**What**: Thousands of Problems for Theorem Provers (20,000+ problems)

**Integration**:
```rust
// src/rust/import/tptp.rs
pub fn import_tptp(file: &Path) -> Result<Theorem> {
    let content = std::fs::read_to_string(file)?;

    // Parse TPTP format
    let parser = TPTPParser::new();
    let problem = parser.parse(&content)?;

    // Convert to ECHIDNA format
    Theorem {
        name: problem.name,
        premises: problem.axioms.into_iter().map(convert_formula).collect(),
        goal: convert_formula(&problem.conjecture),
        prover: ProverHint::Auto,
    }
}
```

**Use Cases**:
- Test ECHIDNA on standard benchmarks
- Compare performance with other ATPs
- Access curated problem sets

**Timeline**: 1-2 months

---

### 5.3 Proof Translation Between Systems

**Problem**: Have Coq proof, need Lean version

**Solution**: Automated translation

**Example**:
```coq
(* Coq *)
Theorem add_comm : forall n m, n + m = m + n.
Proof. intros. ring. Qed.
```
↓ Translate ↓
```lean
-- Lean
theorem add_comm : ∀ n m : ℕ, n + m = m + n := by
  intros
  ring
```

**Challenges**:
- Tactic semantics differ (Coq `ring` ≠ Lean `ring`)
- Type systems differ (universe levels)
- Library APIs differ

**Approach**: Abstract Syntax Tree mapping
```rust
match coq_tactic {
    "intros" => lean_tactic("intros"),
    "ring" => lean_tactic("ring"),
    "simpl" => lean_tactic("simp"),
    "reflexivity" => lean_tactic("rfl"),
    // ... mapping table
}
```

**Timeline**: 6-12 months (complex)

---

## 6. Community & Ecosystem

### 6.1 Proof Marketplace

**Concept**: Buy/sell proof libraries

**Example**:
```
┌────────────────────────────────────────────┐
│ ECHIDNA Proof Marketplace                 │
├────────────────────────────────────────────┤
│                                            │
│ 🔥 Trending Libraries:                     │
│                                            │
│ • Graph Theory Proofs (245 theorems)      │
│   $29.99  ⭐⭐⭐⭐⭐ (127 reviews)         │
│   [Add to Cart]                            │
│                                            │
│ • Linear Algebra Lemmas (512 proofs)      │
│   $49.99  ⭐⭐⭐⭐☆ (89 reviews)          │
│   [Add to Cart]                            │
│                                            │
│ • Number Theory Collection (1,043 proofs) │
│   $99.99  ⭐⭐⭐⭐⭐ (203 reviews)        │
│   [Add to Cart]                            │
│                                            │
└────────────────────────────────────────────┘
```

**Revenue Model**: 70% creator, 30% platform

**Benefits**:
- Incentivizes high-quality proofs
- Builds comprehensive libraries
- Sustainable ecosystem

**Timeline**: 6-9 months (legal + platform)

---

### 6.2 Collaborative Proving

**Concept**: Google Docs for proofs

**Features**:
- **Real-time collaboration** (multiple cursors)
- **Comments** ("Why did you use this tactic?")
- **Suggestions** ("Try `induction` here")
- **Version history** (rollback to previous states)

**Architecture**:
```
┌──────────┐         ┌──────────┐
│  User A  │◄───────►│  Server  │
└──────────┘         └────┬─────┘
                          │
┌──────────┐              │
│  User B  │◄─────────────┘
└──────────┘

WebSocket: Real-time proof state sync
CRDT: Conflict-free replicated data types
```

**Timeline**: 4-6 months

---

### 6.3 Proof Review System

**Concept**: Code review for proofs

**Workflow**:
1. Submit proof for review
2. Reviewers comment on steps
3. Author addresses feedback
4. Approval → merge to library

**UI**:
```
┌─────────────────────────────────────────────┐
│ Proof Review: commutativity_of_addition    │
├─────────────────────────────────────────────┤
│ @alice requested review from @bob           │
│                                             │
│  1  Theorem add_comm : ∀n m, n+m = m+n.    │
│  2  Proof.                                  │
│  3    intros n m.                           │
│  4    induction n.  ← @bob: Why not on m?  │
│  5    - reflexivity.                        │
│  6    - simpl. rewrite IHn. reflexivity.    │
│  7  Qed.                                    │
│                                             │
│ @alice replied: Induction on n is simpler  │
│ because addition is defined recursively    │
│ on the first argument.                      │
│                                             │
│ [@bob approved ✓]  [Merge]                 │
└─────────────────────────────────────────────┘
```

**Timeline**: 3-4 months

---

## 7. Safety & Security Hardening

### 7.1 Adversarial Testing

**Goal**: Try to break the system

**Attack Vectors**:
1. **Malicious proofs** (infinite loops)
2. **Resource exhaustion** (memory bombs)
3. **Proof obfuscation** (deliberately confusing)
4. **Supply chain** (compromised prover binaries)

**Defenses**:

**Timeout enforcement**:
```rust
use tokio::time::{timeout, Duration};

async fn prove_with_timeout(goal: &str) -> Result<Proof> {
    timeout(Duration::from_secs(60), prove(goal))
        .await
        .map_err(|_| Error::Timeout)?
}
```

**Memory limits** (cgroups):
```bash
# Limit prover to 1GB RAM
cgcreate -g memory:echidna
echo 1073741824 > /sys/fs/cgroup/memory/echidna/memory.limit_in_bytes
cgexec -g memory:echidna ./prove_theorem
```

**Sandboxing** (Landlock LSM):
```rust
use landlock::*;

// Restrict filesystem access
let abi = ABI::V2;
Ruleset::new()
    .handle_access(AccessFs::Execute)?
    .create()?
    .add_rule(PathFd::new("/usr/bin/coqc")?)?
    .restrict_self()?;

// Now process can only execute Coq compiler
```

**Timeline**: 2-3 months

---

### 7.2 Proof Obfuscation Detection

**Attack**: Deliberately confusing proof that's technically valid

**Example**:
```coq
(* Obfuscated proof *)
Theorem t : 2 + 2 = 4.
Proof.
  assert (H1: 1 + 1 = 2) by reflexivity.
  assert (H2: 2 + 1 = 3) by reflexivity.
  assert (H3: 3 + 1 = 4) by reflexivity.
  assert (H4: 1 + 1 + 1 = 3) by reflexivity.
  assert (H5: 1 + 1 + 1 + 1 = 4) by reflexivity.
  (* ... 100 more useless assertions ... *)
  reflexivity.
Qed.

(* vs. simple proof *)
Theorem t : 2 + 2 = 4.
Proof. reflexivity. Qed.
```

**Detection**:
```rust
pub fn detect_obfuscation(proof: &Proof) -> ObfuscationScore {
    let mut score = 0.0;

    // Red flag 1: Too many tactics for simple goal
    if proof.tactics.len() > expected_complexity(&proof.goal) * 3 {
        score += 0.3;
    }

    // Red flag 2: Unused hypotheses
    let used = count_used_hypotheses(&proof);
    let total = proof.hypotheses.len();
    if used < total / 2 {
        score += 0.2;
    }

    // Red flag 3: Circular dependencies
    if has_circular_tactics(&proof) {
        score += 0.5;
    }

    ObfuscationScore(score)
}
```

**Timeline**: 2-3 months

---

## 8. Research Extensions

### 8.1 Probabilistic Proofs (DeepProbLog)

**Already planned** in roadmap, but worth detailing:

```prolog
% DeepProbLog: Probabilistic logic programming
% Combine neural networks with logic

% Neural network predicts tactic probability
nn(tactic_model, [GoalEmbedding], Tactic, TacticProb).

% Proof search with probabilities
proof(Goal, []) :-
    base_case(Goal).

proof(Goal, [Tactic|Rest]) :-
    nn(tactic_model, [Goal], Tactic, P),
    P > 0.5,  % Only try high-confidence tactics
    apply_tactic(Tactic, Goal, Subgoals),
    maplist(proof, Subgoals, Subproofs),
    append(Subproofs, Rest).
```

**Benefits**:
- Probabilistic reasoning (confidence scores)
- Neural guidance (ML suggests tactics)
- Logic guarantees (only valid proofs succeed)

**Timeline**: 6-12 months (research project)

---

### 8.2 Homotopy Type Theory (HoTT)

**Why**: Foundation for modern mathematics

**What**: Types = spaces, terms = points, equality = paths

**Example** (Cubical Agda):
```agda
-- Univalence axiom (computational!)
ua : {A B : Type} → (A ≃ B) → A ≡ B

-- Function extensionality
funExt : {A B : Type} {f g : A → B}
       → ((x : A) → f x ≡ g x)
       → f ≡ g
```

**ECHIDNA Integration**:
- Add Cubical Agda as 13th prover
- Support higher inductive types
- Implement path induction

**Timeline**: 12+ months (advanced research)

---

## 9. Implementation Priority Matrix

| Feature | Impact | Effort | Priority | Timeline |
|---------|--------|--------|----------|----------|
| **RL Tactic Agent** | High | High | Medium | 3-6 months |
| **GNN Proof States** | High | High | Medium | 4-6 months |
| **Transformer Premises** | High | Very High | Low | 6-12 months |
| **Active Learning** | Medium | Medium | High | 2-3 months |
| **Proof Repair** | High | Medium | High | 3-4 months |
| **Proof Minimization** | Medium | Low | High | 1-2 months |
| **Counterexamples** | High | Medium | Medium | 2-3 months |
| **Distributed Search** | High | High | Medium | 3-6 months |
| **Cloud Functions** | Medium | Medium | Medium | 2-3 months |
| **Proof Cache** | High | Low | High | 1-2 months |
| **Visual Editor** | High | Very High | Medium | 6-9 months |
| **NL Explanations** | Medium | High | Low | 4-6 months |
| **Learning Mode** | Medium | Medium | Medium | 3-4 months |
| **SMT-LIB Export** | Low | Low | High | 2-3 months |
| **TPTP Import** | Medium | Low | High | 1-2 months |
| **Proof Translation** | Low | Very High | Low | 6-12 months |
| **Marketplace** | Medium | High | Low | 6-9 months |
| **Collaborative** | Medium | High | Low | 4-6 months |
| **Proof Review** | Low | Medium | Low | 3-4 months |
| **Adversarial Test** | High | Medium | High | 2-3 months |
| **DeepProbLog** | High | Very High | Medium | 6-12 months |

---

## 10. Recommended Immediate Next Steps

Based on **high impact, low-to-medium effort**:

### Phase A: Quick Wins (1-3 months)
1. ✅ **Proof minimization** - reduce bloated proofs
2. ✅ **Proof cache** - speed up common lemmas
3. ✅ **TPTP import** - access benchmark suite
4. ✅ **SMT-LIB export** - interop with SMT solvers
5. ✅ **Adversarial testing** - harden security

### Phase B: High Impact (3-6 months)
1. ✅ **Active learning** - human feedback loop
2. ✅ **Proof repair** - auto-fix broken proofs
3. ✅ **Counterexamples** - show why unprovable
4. ✅ **Distributed search** - scale to cluster
5. ✅ **Cloud deployment** - serverless infrastructure

### Phase C: Research (6-12 months)
1. ✅ **RL tactic agent** - learn from experience
2. ✅ **GNN proof states** - structured representations
3. ✅ **Visual editor** - professional IDE
4. ✅ **DeepProbLog** - probabilistic reasoning

### Phase D: Ecosystem (ongoing)
1. ✅ **Community features** - marketplace, collaboration
2. ✅ **Educational content** - tutorials, examples
3. ✅ **Documentation** - comprehensive guides
4. ✅ **Benchmark suite** - continuous testing

---

## Conclusion

ECHIDNA has a **rich future roadmap** spanning:
- **ML innovation** (RL, GNNs, transformers)
- **Proof automation** (repair, minimization, counterexamples)
- **Scalability** (distributed, cloud, caching)
- **User experience** (visual editor, explanations, learning)
- **Ecosystem** (marketplace, collaboration, standards)
- **Research** (HoTT, probabilistic logic, adversarial robustness)

**The path forward**:
1. Start with quick wins (cache, minimization, TPTP)
2. Build high-impact features (repair, counterexamples, active learning)
3. Invest in research (RL, GNNs, DeepProbLog)
4. Grow the ecosystem (community, marketplace, standards)

This roadmap takes ECHIDNA from a **powerful research prototype** to a **world-class automated reasoning platform** used by researchers, students, and industry alike.

---

*ECHIDNA Future Development Roadmap*
*Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>*
