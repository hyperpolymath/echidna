# Training Data Expansion Guide

**Current Status**: 107 proofs, 585 tactics, 148 premises
**Target**: 1000+ proofs, 5000+ tactics, 500+ premises

---

## 📊 Current Dataset Analysis

### Coverage by Prover
```
Coq:      74 proofs (69%)  ← Good coverage
ACL2:     11 proofs (10%)
Mizar:     7 proofs (7%)
Lean:      5 proofs (5%)
Isabelle:  4 proofs (4%)
Agda:      4 proofs (4%)
Z3:        1 proof  (1%)   ← Needs expansion
CVC5:      1 proof  (1%)   ← Needs expansion
```

### Gaps to Fill
1. **Unbalanced**: 69% Coq, need more diversity
2. **Missing tiers**: Z3, CVC5 severely under-represented
3. **Limited domains**: Need more algebraic, geometric, inductive proofs
4. **Small vocabulary**: Only 62 words for premise selection

---

## 🎯 Expansion Strategy

### Phase 1: Mine Existing ECHIDNA Examples (Quick Win)
**Location**: `proofs/` directory in ECHIDNA repo
**Estimated**: +50 proofs

```bash
# Already have these files but not yet extracted:
proofs/
├── acl2/        # 5 files with ~15 proofs
├── agda/        # 10 files with ~25 proofs
├── coq/         # 20+ files with ~80 proofs
├── cvc5/        # 3 files with ~8 proofs
├── hol-light/   # 5 files with ~12 proofs
├── hol4/        # 5 files with ~15 proofs
├── isabelle/    # 8 files with ~20 proofs
├── lean/        # 15+ files with ~40 proofs
├── metamath/    # 10 files with ~30 proofs
├── mizar/       # 5 files with ~10 proofs
├── pvs/         # 5 files with ~15 proofs
└── z3/          # 5 files with ~12 proofs
```

**Action**: Update `src/julia/extract_training_data.jl` to scan all proof files.

### Phase 2: Standard Library Mining (Medium Effort)
**Estimated**: +500-1000 proofs

#### Coq Standard Library
```bash
# Download Coq stdlib
git clone https://github.com/coq/coq.git
cd coq/theories

# Rich sources:
theories/Init/        # 50+ basic proofs
theories/Arith/       # 200+ arithmetic proofs
theories/Lists/       # 150+ list proofs
theories/Logic/       # 100+ logic proofs
theories/Sets/        # 80+ set theory proofs
theories/Reals/       # 300+ real analysis proofs
```

#### Lean Mathlib
```bash
# Download Lean mathlib (huge!)
git clone https://github.com/leanprover-community/mathlib4.git

# High-value files:
Mathlib/Algebra/      # 2000+ algebraic proofs
Mathlib/Data/         # 1500+ data structure proofs
Mathlib/Logic/        # 500+ logic proofs
Mathlib/Tactic/       # 300+ tactic examples
```

#### Isabelle Archive of Formal Proofs
```bash
# Download AFP
git clone https://github.com/isabelle-prover/afp-devel.git

# Selected entries:
afp/thys/AVL-Trees/           # 50+ tree proofs
afp/thys/Abstract-Rewriting/  # 80+ rewriting proofs
afp/thys/Algebra/             # 200+ algebra proofs
```

### Phase 3: Proof Corpuses (High Value)
**Estimated**: +2000+ proofs

#### 1. **CoqGym** (Facebook Research)
- **Size**: 71,000 proofs from 123 Coq projects
- **URL**: https://github.com/princeton-vl/CoqGym
- **Format**: JSON with proof states and tactics
- **Quality**: High - already preprocessed
- **License**: MIT

```bash
git clone https://github.com/princeton-vl/CoqGym.git
# Extract from data/projects/
# Each project has proofs.json with full traces
```

#### 2. **HOList** (HOL Light)
- **Size**: 29,000 proofs
- **URL**: https://github.com/tensorflow/deepmath/tree/master/hol-light
- **Format**: S-expressions with proof trees
- **Quality**: High

#### 3. **Lean Mathlib Tactics**
- **Size**: 100,000+ tactic applications
- **URL**: https://github.com/leanprover-community/mathlib-tools
- **Tool**: `lean --export` to extract proof terms
- **Quality**: Excellent

#### 4. **IsarMathLib** (Isabelle)
- **Size**: 3,000+ structured proofs
- **URL**: https://isarmathlib.org/
- **Format**: Isar structured proofs
- **Quality**: High - well-documented

#### 5. **Mizar Mathematical Library**
- **Size**: 12,000+ articles, 60,000+ theorems
- **URL**: http://mizar.org/library/
- **Format**: .miz files
- **Quality**: High - peer-reviewed

#### 6. **MetaMath Proof Explorer**
- **Size**: 30,000+ theorems
- **URL**: http://us.metamath.org/
- **Format**: .mm database
- **Quality**: Excellent - complete proof trees

#### 7. **ACL2 Community Books**
- **Size**: 5,000+ proofs
- **URL**: https://github.com/acl2/acl2
- **Path**: books/ directory
- **Quality**: Good

#### 8. **PVS NASA Libraries**
- **Size**: 2,000+ proofs
- **URL**: https://github.com/nasa/pvslib
- **Format**: .pvs files
- **Quality**: High - aerospace-grade

---

## 🔧 Implementation Plan

### Step 1: Update Data Extraction Script

**File**: `src/julia/extract_training_data.jl`

Add support for multiple sources:

```julia
# SPDX-License-Identifier: MIT OR Palimpsest-0.6

"""
Enhanced training data extraction for ECHIDNA v1.4

Supports:
- Local proof files (proofs/)
- CoqGym JSON format
- Lean export format
- Isabelle PIDE output
- Standard library parsing
"""

# Data source configuration
const DATA_SOURCES = [
    # Local proofs (already implemented)
    (type="local", path="proofs/", enabled=true),

    # CoqGym corpus
    (type="coqgym", path="../coqgym/data/projects/", enabled=false),

    # Lean mathlib
    (type="lean_export", path="../mathlib4/", enabled=false),

    # Isabelle AFP
    (type="isabelle_afp", path="../afp-devel/thys/", enabled=false),

    # Metamath
    (type="metamath", path="../metamath/set.mm", enabled=false),
]

# Prover-specific extractors
function extract_coqgym(project_dir)
    proofs = []
    for file in readdir(joinpath(project_dir, "data"))
        if endswith(file, "proofs.json")
            data = JSON3.read(read(joinpath(project_dir, "data", file), String))
            for proof in data["proofs"]
                push!(proofs, (
                    prover="Coq",
                    theorem=proof["name"],
                    goal=proof["goal"],
                    tactics=[step["tactic"] for step in proof["steps"]],
                    premises=[step["context"] for step in proof["steps"]]
                ))
            end
        end
    end
    return proofs
end

function extract_lean_export(file_path)
    # Parse Lean .olean or .ast files
    # Extract tactic applications from proof terms
    # Return structured proof data
end

function extract_isabelle_afp(theory_file)
    # Parse .thy files
    # Extract Isar proof steps
    # Map to tactic applications
end

function extract_metamath(mm_file)
    # Parse .mm database
    # Extract proof steps
    # Map to tactic-like operations
end
```

### Step 2: Batch Download Script

```bash
#!/bin/bash
# download_proof_corpora.sh

ECHIDNA_ROOT="/var/home/hyper/Documents/hyperpolymath-repos/echidna"
DATA_DIR="$ECHIDNA_ROOT/external_corpora"

mkdir -p "$DATA_DIR"
cd "$DATA_DIR"

echo "Downloading proof corpora for ECHIDNA training..."

# CoqGym (2.4 GB)
if [ ! -d "CoqGym" ]; then
    echo "Downloading CoqGym..."
    git clone --depth 1 https://github.com/princeton-vl/CoqGym.git
fi

# Lean mathlib (1.2 GB)
if [ ! -d "mathlib4" ]; then
    echo "Downloading Lean mathlib..."
    git clone --depth 1 https://github.com/leanprover-community/mathlib4.git
fi

# Isabelle AFP (500 MB)
if [ ! -d "afp-devel" ]; then
    echo "Downloading Isabelle AFP..."
    git clone --depth 1 https://github.com/isabelle-prover/afp-devel.git
fi

# Metamath (50 MB)
if [ ! -d "metamath" ]; then
    echo "Downloading Metamath..."
    git clone --depth 1 https://github.com/metamath/set.mm.git metamath
fi

# ACL2 books (200 MB)
if [ ! -d "acl2" ]; then
    echo "Downloading ACL2 books..."
    git clone --depth 1 https://github.com/acl2/acl2.git
fi

# PVS NASA libraries (100 MB)
if [ ! -d "pvslib" ]; then
    echo "Downloading PVS libraries..."
    git clone --depth 1 https://github.com/nasa/pvslib.git
fi

echo "✓ Download complete!"
echo "Total size: ~4.5 GB"
echo "Estimated proofs: 100,000+"
```

### Step 3: Incremental Training Pipeline

```julia
# src/julia/incremental_training.jl

"""
Incremental model training for ECHIDNA

Train models in batches to avoid memory issues with large datasets
"""

function train_incremental(
    data_sources::Vector,
    batch_size::Int=1000,
    checkpoint_every::Int=10
)
    model = initialize_model()

    total_proofs = 0
    for (batch_num, batch) in enumerate(batches(data_sources, batch_size))
        @info "Training batch $batch_num ($(length(batch)) proofs)"

        # Extract features
        X, y = prepare_batch(batch)

        # Update model (online learning)
        update_model!(model, X, y)

        total_proofs += length(batch)

        # Checkpoint
        if batch_num % checkpoint_every == 0
            save_checkpoint(model, "checkpoint_batch_$batch_num.jlso")
            evaluate_model(model, validation_set)
        end
    end

    @info "Training complete: $total_proofs proofs processed"
    return model
end
```

### Step 4: Quality Filtering

```julia
# Filter low-quality proofs
function filter_proofs(proofs)
    filtered = []
    for proof in proofs
        # Skip if too short (trivial)
        length(proof.tactics) < 2 && continue

        # Skip if too long (likely generated/unnatural)
        length(proof.tactics) > 100 && continue

        # Skip if uses deprecated tactics
        any(t -> t in DEPRECATED_TACTICS, proof.tactics) && continue

        # Skip if parsing errors
        all(isvalid, proof.tactics) || continue

        push!(filtered, proof)
    end
    return filtered
end
```

---

## 📈 Expected Results

### After Phase 1 (Local Mining)
- **Proofs**: 107 → 150 (+40%)
- **Tactics**: 585 → 800 (+37%)
- **Premises**: 148 → 200 (+35%)
- **Time**: 1 hour
- **Cost**: Free

### After Phase 2 (Standard Libraries)
- **Proofs**: 150 → 650 (+333%)
- **Tactics**: 800 → 3000 (+275%)
- **Premises**: 200 → 400 (+100%)
- **Time**: 1 week
- **Cost**: Free

### After Phase 3 (Proof Corpora)
- **Proofs**: 650 → 5000+ (+669%)
- **Tactics**: 3000 → 20000+ (+567%)
- **Premises**: 400 → 2000+ (+400%)
- **Time**: 2-4 weeks
- **Cost**: Free (+ compute for training)

---

## 🎯 Recommended Priorities

### Week 1: Quick Wins
1. ✅ Mine existing `proofs/` directory (all 12 provers)
2. ✅ Download CoqGym (easiest to parse, pre-formatted)
3. ✅ Extract Lean mathlib tactics
4. ✅ Retrain models with expanded dataset

### Week 2-3: Quality Expansion
1. Parse Isabelle AFP theories
2. Extract Metamath proof database
3. Mine Coq standard library
4. Add data augmentation (tactic reordering, paraphrasing)

### Week 4-6: Scale Up
1. Implement distributed extraction (parallel processing)
2. Train larger models (Flux.jl transformers)
3. Add active learning (prioritize hard examples)
4. Benchmark on held-out test set

---

## 🔬 Data Augmentation Techniques

### 1. Tactic Reordering
```julia
# Some tactics commute (e.g., intro x, intro y)
# Generate variations
original = ["intro x", "intro y", "reflexivity"]
augmented = ["intro y", "intro x", "reflexivity"]
```

### 2. Premise Paraphrasing
```julia
# Use theorem aliases
original = "apply Nat.add_comm"
variations = [
    "apply plus_comm",
    "apply addition_commutative",
    "rewrite Nat.add_comm"
]
```

### 3. Synthetic Proof Generation
```julia
# Generate simple proofs programmatically
function generate_arithmetic_proofs(n=1000)
    proofs = []
    for i in 1:n
        a, b = rand(1:100, 2)
        proof = (
            goal="$a + $b = $b + $a",
            tactics=["intro", "simpl", "rewrite Nat.add_comm", "reflexivity"],
            prover="Coq"
        )
        push!(proofs, proof)
    end
    return proofs
end
```

### 4. Cross-Prover Translation
```julia
# Map Coq proofs to Lean equivalents
coq_proof = "intros. reflexivity."
lean_proof = "intro. rfl"
# Use for transfer learning
```

---

## 📝 Practical Next Steps

### Immediate (Today)
```bash
cd /var/home/hyper/Documents/hyperpolymath-repos/echidna

# 1. Mine existing proof files
julia --project=src/julia -e 'include("src/julia/extract_training_data.jl");
    extract_all_proofs("proofs/")'

# 2. Check new dataset size
wc -l training_data/*.jsonl
```

### This Week
```bash
# 3. Download CoqGym
mkdir -p external_corpora
cd external_corpora
git clone --depth 1 https://github.com/princeton-vl/CoqGym.git

# 4. Extract CoqGym data
julia --project=../src/julia -e 'include("../src/julia/extract_coqgym.jl")'

# 5. Retrain with expanded dataset
julia --project=src/julia src/julia/train_models.jl
```

### This Month
```bash
# 6. Add Lean mathlib
git clone --depth 1 https://github.com/leanprover-community/mathlib4.git

# 7. Implement quality filtering
julia --project=src/julia -e 'include("src/julia/filter_proofs.jl")'

# 8. Train larger model
julia --project=src/julia -e 'include("src/julia/train_transformer.jl")'
```

---

## 🎓 Learning Resources

### Proof Mining Tutorials
- **CoqGym Paper**: "Learning to Prove Theorems via Interacting with Proof Assistants"
- **HOList**: "Deep Reinforcement Learning for Tactical Theorem Proving"
- **GamePad**: "Learning to Reason in Large Theories without Imitation"

### Datasets
- **PISA**: Proof artifact co-training (Isabelle)
- **LeanStep**: Single-step tactic prediction
- **ProverBot9001**: Coq proof synthesis

### Tools
- **SerAPI**: Coq serialization API
- **Lean export**: Proof term extraction
- **Isabelle PIDE**: Interactive theorem proving

---

## 💡 Pro Tips

1. **Start Small**: Verify extraction on 10-100 proofs before scaling
2. **Version Control**: Tag each dataset version (v1.3-base, v1.4-coqgym, etc.)
3. **Validation Set**: Hold out 10-20% for testing
4. **Monitor Quality**: Track vocabulary size, tactic diversity, success rate
5. **Incremental**: Add sources one at a time, retrain, evaluate
6. **Document**: Keep provenance metadata (source, date, license)

---

## 📊 Success Metrics

Track these metrics after expansion:

| Metric | Current | Target | Impact |
|--------|---------|--------|--------|
| Total Proofs | 107 | 5,000+ | Model generalization |
| Tactics | 585 | 20,000+ | Better predictions |
| Vocabulary | 62 | 500+ | Premise selection |
| Prover Balance | 69% Coq | <30% any | Fairness |
| Avg Confidence | 0.65 | 0.80+ | Model certainty |
| Top-3 Accuracy | ~40% | 70%+ | User success |

---

**Ready to expand! Start with Phase 1 today for quick wins.** 🚀
