# Traceability Matrix: ParadisEO Integration

This document provides a clear traceability path for humans and bots to navigate the ParadisEO metaheuristic integration work across the hyperpolymath ecosystem.

## Overview

All ParadisEO-related development is coordinated through a **hub-and-spoke** model:

- **Hub**: `echidna/.github/ROADMAP-PARADISEO.md` - Master roadmap coordinating all work
- **Spokes**: Individual issue files in each repository, cross-linked to the hub and to each other

## Navigation Structure

### 1. Master Roadmap (Hub)

**Location**: `hyperpolymath/echidna/.github/ROADMAP-PARADISEO.md`

**Purpose**: Single source of truth for all ParadisEO integration efforts across the ecosystem

**Contents**:
- Issue Index table with hyperlinks to all individual issues
- Detailed specifications for each issue
- Cross-references between related issues
- Labels and metadata for filtering

### 2. Individual Issue Files (Spokes)

#### echidna Repository

All echidna issues are stored in `.github/issues/` with local relative links:

| ID | File | Local Link | Cross-Repo Links |
|----|------|------------|------------------|
| ECH-01 | echidna-01-pareto-moeo.md | [link](./issues/echidna-01-pareto-moeo.md) | → PB-01, PB-02, EB-01 |
| ECH-02 | echidna-02-cmaes-julia-gnn.md | [link](./issues/echidna-02-cmaes-julia-gnn.md) | → PB-01, EB-01 |
| ECH-03 | echidna-03-chapel-island-migration.md | [link](./issues/echidna-03-chapel-island-migration.md) | → PB-01, PB-02, EB-01 |
| ECH-04 | echidna-04-ffi-abi-bridge.md | [link](./issues/echidna-04-ffi-abi-bridge.md) | → ECH-01, ECH-02, ECH-03, PB-01, PB-02 |

Each issue file contains:
- Full feature specification
- Cross-references to related issues (both intra-repo and inter-repo)
- Links back to the master roadmap
- Repository navigation links

#### echidnabot Repository

**Location**: `.github/ISSUE_TEMPLATE/feature_request.yml`

**Purpose**: Issue template with embedded issues list

**Contents**:
- EB-01: feat(dispatcher) - adaptive portfolio timeout and solver selection (filed as [#177](https://github.com/hyperpolymath/echidnabot/issues/177))
- Navigation section linking to the master roadmap
- Cross-references to echidna ECH-01 through ECH-04

**GitHub URL**: `https://github.com/hyperpolymath/echidnabot/blob/main/.github/ISSUE_TEMPLATE/feature_request.yml`

#### proof-burrower Repository

**Location**: Issues filed in hyperpolymath/proof-burrower repository

**Issues**:
- PB-01: feat(swarm) - combinatorial tactic playbook synthesis ([#108](https://github.com/hyperpolymath/proof-burrower/issues/108))
- PB-02: feat(ledger) - anti-pattern mining and objective fitness formulation ([#109](https://github.com/hyperpolymath/proof-burrower/issues/109))

**Status**: Both issues filed and ready for implementation

**GitHub URLs**:
- PB-01: https://github.com/hyperpolymath/proof-burrower/issues/108
- PB-02: https://github.com/hyperpolymath/proof-burrower/issues/109

## Traceability for Humans

### Path 1: Top-Down (Roadmap → Issue → Implementation)

```
Master Roadmap (ROADMAP-PARADISEO.md)
    ↓ (click issue ID in table)
Individual Issue File (e.g., echidna-01-pareto-moeo.md)
    ↓ (follow Related Issues links)
Related Issues in same or other repos
    ↓ (follow File links)
Source code locations
```

### Path 2: Bottom-Up (Code → Issue → Roadmap)

```
Source file (e.g., verification/pareto.rs)
    ↓ (check header comments for issue reference)
Issue ID (e.g., ECH-01)
    ↓ (search in master roadmap)
Master Roadmap (ROADMAP-PARADISEO.md)
    ↓ (see all related work)
Full ecosystem context
```

## Traceability for Bots

### Machine-Readable Links

All issue files use **relative markdown links** for intra-repo navigation:
```markdown
[ECH-01](./issues/echidna-01-pareto-moeo.md)
```

All cross-repo links use **absolute GitHub URLs**:
```markdown
[EB-01](https://github.com/hyperpolymath/echidnabot/blob/main/.github/ISSUE_TEMPLATE/feature_request.yml)
```

### File Structure Convention

```
.github/
├── ROADMAP-PARADISEO.md          # Master coordination
├── TRACEABILITY.md               # This document
├── ISSUE_TEMPLATE/
│   └── FEATURES.md               # Aggregated issues list (echidna)
└── issues/
    ├── echidna-01-pareto-moeo.md
    ├── echidna-02-cmaes-julia-gnn.md
    ├── echidna-03-chapel-island-migration.md
    └── echidna-04-ffi-abi-bridge.md
```

### ID Convention

- **Prefix**: Repository code (ECH, PB, EB)
- **Number**: Sequential within repo
- **Format**: `[PREFIX]-[NUMBER]`

## Verification Checklist

### ✅ echidna Repository
- [x] Master roadmap exists: `.github/ROADMAP-PARADISEO.md`
- [x] Individual issue files exist: `.github/issues/echidna-{01,02,03,04}-*.md`
- [x] All issues have IDs matching roadmap table
- [x] Roadmap table has clickable links to all issue files
- [x] Each issue file links back to roadmap
- [x] Each issue file has cross-references to related issues

### ✅ echidnabot Repository
- [x] Feature template exists: `.github/ISSUE_TEMPLATE/feature_request.yml`
- [x] EB-01 issue is documented in the template
- [x] EB-01 filed as GitHub issue [#177](https://github.com/hyperpolymath/echidnabot/issues/177)
- [x] Navigation links to master roadmap
- [x] Cross-references to echidna issues

### ✅ proof-burrower Repository
- [x] PB-01 filed as GitHub issue [#108](https://github.com/hyperpolymath/proof-burrower/issues/108)
- [x] PB-02 filed as GitHub issue [#109](https://github.com/hyperpolymath/proof-burrower/issues/109)
- [x] Cross-references to echidna issues added
- [x] All claims verified against upstream (be897dd07e1a16014f2d0f8d9cbedffb0240dd4a)

## Query Paths

### GitHub Search

To find all ParadisEO-related work:
```
repo:hyperpolymath/echidna "ParadisEO" OR "ECH-01" OR "ECH-02" OR "ECH-03" OR "ECH-04"
repo:hyperpolymath/echidnabot "ParadisEO" OR "EB-01"
repo:hyperpolymath/proof-burrower "ParadisEO" OR "PB-01" OR "PB-02"
```

### File System Navigation

From echidna repo root:
```bash
# View master roadmap
cat .github/ROADMAP-PARADISEO.md

# View all echidna issues
ls -la .github/issues/

# View a specific issue
cat .github/issues/echidna-01-pareto-moeo.md
```

### Bot Access Patterns

1. **List all issues**: Parse ROADMAP-PARADISEO.md table
2. **Get issue details**: Follow markdown links from table
3. **Find related work**: Parse "Related Issues" section in each issue file
4. **Navigate to code**: Use "Area" field to locate source files

## Maintainers Guide

### Adding a New Issue

1. Create individual issue file in `.github/issues/[REPO]-[NUMBER]-[slug].md`
2. Add entry to ROADMAP-PARADISEO.md Issue Index table
3. Add detailed specification under appropriate repo section
4. Link to related issues in "Related Issues" section
5. Ensure all cross-references are bidirectional

### Updating an Issue

1. Update the individual issue file
2. If status changes, update ROADMAP-PARADISEO.md
3. Verify all cross-references still valid
4. Update "Last Updated" date

---

**Document Version**: 1.1  
**Last Updated**: 2026-10-09  
**Owner**: hyperpolymath/echidna maintainers  
**Related**: [ROADMAP-PARADISEO.md](./ROADMAP-PARADISEO.md)
**GitHub Issues Filed**: ECH-01→#420, ECH-02→#421, ECH-03→#422, ECH-04→#424, PB-01→#108, PB-02→#109, EB-01→#177
