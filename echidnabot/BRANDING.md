# echidnabot Branding Guide

## Repository Description

**Short (GitHub limit ~350 chars):**

> Proof-aware CI bot that automatically verifies mathematical theorems in your codebase. Integrates with GitHub/GitLab/Bitbucket to run formal verification on every push and PR using ECHIDNA's multi-prover backend (Coq, Lean, Agda, Isabelle, Z3, and more). Written in Rust.

**Extended:**

> ECHIDNABOT is an intelligent CI orchestration layer for formal mathematics and verified software. When you push code containing formal proofs—whether in Coq, Lean 4, Agda, Isabelle/HOL, Z3, Metamath, or other theorem provers—echidnabot automatically dispatches verification jobs to ECHIDNA Core and reports results directly in your pull requests. Think of it as "GitHub Actions for mathematical certainty."
>
> Built entirely in Rust with async Tokio, Axum, and GraphQL, it's designed for correctness, security, and scalability. Multi-platform support (GitHub, GitLab, Bitbucket, Codeberg), multi-prover verification, and ML-powered tactic suggestions make it the definitive CI solution for proof-carrying code.

---

## Repository Topics/Tags

### GitHub Topics (use all that apply)

**Primary Tags:**
```
theorem-prover
formal-verification
ci-cd
proof-assistant
rust
```

**Domain Tags:**
```
formal-methods
type-theory
dependent-types
mathematics
logic
computer-science
```

**Technology Tags:**
```
rust-lang
tokio
axum
graphql
async-graphql
octocrab
```

**Prover Ecosystem Tags:**
```
coq
lean
lean4
agda
isabelle
z3
smt
metamath
hol
```

**Integration Tags:**
```
github-app
github-actions
gitlab-ci
webhook
ci-bot
devops
automation
```

**Quality Tags:**
```
hacktoberfest
good-first-issue
help-wanted
```

### Complete GitHub Topics List (Copy-Paste Ready)

```
theorem-prover, formal-verification, ci-cd, proof-assistant, rust, formal-methods, dependent-types, coq, lean, lean4, agda, isabelle, z3, smt, metamath, graphql, github-app, webhook, ci-bot, automation, rust-lang, mathematics, logic, tokio, axum
```

### GitLab Topics

```
theorem-prover, formal-verification, ci-cd, rust, coq, lean, agda, isabelle, z3, graphql, automation
```

### Crates.io Categories

```toml
categories = ["development-tools", "science", "command-line-utilities", "web-programming"]
keywords = ["theorem-prover", "formal-verification", "ci", "proof-assistant", "echidna"]
```

---

## Visual Branding Assets

### Color Palette

| Color       | Hex       | Use Case                          |
|-------------|-----------|-----------------------------------|
| Deep Indigo | `#1a1a2e` | Primary background                |
| Royal Blue  | `#4361ee` | Primary accent, verified state    |
| Electric Cyan | `#00d9ff` | Highlights, active elements      |
| Pure White  | `#ffffff` | Text on dark, contrast           |
| Success Green | `#00c853` | Proof verified                  |
| Error Red   | `#ff1744` | Proof failed                     |
| Warm Gold   | `#ffd700` | RSR certification badge          |

### Typography

- **Headlines:** JetBrains Mono or Fira Code (monospace, technical)
- **Body:** Inter or Source Sans Pro (clean, readable)
- **Math Notation:** Computer Modern or STIX Two Math

---

## LLM Instructions for Avatar Creation

### Avatar Prompt (Square, 512x512 or 1024x1024)

```
Create a minimalist, geometric logo for "echidnabot" - a theorem-proving CI bot.

CONCEPT:
A stylized echidna (spiny anteater) merged with mathematical/logical symbols.
The echidna represents thorough, methodical proof verification - just as
echidnas use their spines for protection, this bot protects codebases
with formal verification.

DESIGN ELEMENTS:
1. PRIMARY SHAPE: Simplified echidna silhouette or head profile, formed from
   geometric shapes (circles, triangles representing spines)
2. INTEGRATION: Incorporate one of these mathematical symbols subtly:
   - Turnstile (⊢) - the logical "proves" symbol
   - Forall (∀) or Exists (∃) quantifiers
   - Lambda (λ) for computation
   - QED square (∎) for proof completion
3. OPTIONAL: Small gear or circuit pattern to suggest automation/bot nature

STYLE:
- Flat design, no gradients except subtle ones for depth
- Geometric and angular, not cute or cartoonish
- Professional and technical aesthetic
- Should work at 32x32 favicon size and 512x512

COLORS:
- Primary: Deep indigo (#1a1a2e) background
- Secondary: Electric cyan (#00d9ff) for the echidna form
- Accent: Royal blue (#4361ee) for mathematical symbols
- Alternative: Can be designed on white/transparent for versatility

MOOD:
Intelligent, methodical, protective, mathematical precision.
This is a tool for serious formal verification, not a toy.

DO NOT:
- Make it look cute, kawaii, or cartoon-like
- Use photorealistic animal imagery
- Include text in the logo itself
- Use more than 3 colors
- Make it overly complex (should be recognizable at small sizes)

REFERENCE STYLES:
Similar aesthetic to: Rust Foundation logo, Haskell logo,
OCaml logo, NixOS snowflake - clean, geometric, technical.
```

---

## LLM Instructions for Banner Creation

### Banner Prompt (1280x640 for GitHub social preview)

```
Create a GitHub repository banner for "echidnabot" - a proof-aware CI bot
for formal verification.

DIMENSIONS: 1280 x 640 pixels (2:1 aspect ratio)

COMPOSITION (left to right):
1. LEFT THIRD: The echidnabot logo/avatar (the geometric echidna)
2. CENTER: The name "echidnabot" in clean, monospace typography
3. RIGHT THIRD: Abstract representation of proof verification

VISUAL ELEMENTS:

Left Section:
- Place the geometric echidna logo prominently
- Subtle glow or highlight effect around it

Center Section:
- "echidnabot" in JetBrains Mono or similar monospace font
- Below it, smaller tagline: "Proof-Aware CI" or "Verify. Every. Commit."
- Optional: Small icons representing supported platforms (GitHub, GitLab)

Right Section - Choose ONE concept:

OPTION A - "Proof Tree":
- Abstract tree structure with nodes and branches
- Nodes contain mathematical symbols (∀, ∃, λ, →, ⊢)
- Some nodes glow green (verified), most are blue (processing)
- Tree represents proof derivation

OPTION B - "Git + Logic":
- Git commit graph (nodes connected by lines)
- Each commit node has a small checkmark or proof symbol
- Shows the concept: every commit is verified

OPTION C - "Multi-Prover":
- Subtle logos or symbols of theorem provers:
  Coq (rooster silhouette), Lean (∞), Agda (A), Z3, Isabelle
- Arranged in a flowing pattern, all connecting to echidnabot

BACKGROUND:
- Deep indigo (#1a1a2e) to near-black gradient
- Subtle grid pattern (like proof paper or circuit board)
- Optional: very faint mathematical formulas in background

COLOR SCHEME:
- Background: #1a1a2e (deep indigo)
- Primary accent: #00d9ff (electric cyan)
- Secondary: #4361ee (royal blue)
- Text: #ffffff (white)
- Subtle accents: #00c853 (verified green)

TYPOGRAPHY:
- "echidnabot" - Bold monospace, electric cyan or white
- Tagline - Regular weight, slightly smaller, 60% opacity white

STYLE:
- Modern, technical, professional
- Clean lines, geometric shapes
- Dark theme (matches IDE/terminal aesthetics)
- No gradients except subtle background fade
- Should feel like developer tooling, not consumer software

DO NOT:
- Use photorealistic imagery
- Include screenshots or code snippets
- Make it cluttered or busy
- Use more than 4 colors total
- Include version numbers or dates

REFERENCE:
Similar aesthetic to: GitHub's own dark theme banners,
Vercel's marketing materials, Rust project graphics,
JetBrains IDE promotional art.
```

---

## Banner Variants

### Minimal Banner (for platforms with different aspect ratios)

```
Create a minimal banner for echidnabot.

DIMENSIONS: Flexible (provide both 1280x640 and 1500x500)

CONTENT:
- echidnabot logo on left
- "echidnabot" text center-left
- Tagline "Proof-Aware CI for Formal Verification" below
- Deep indigo background (#1a1a2e)
- Electric cyan accents (#00d9ff)

Keep it extremely clean and simple.
```

### Terminal/CLI Styled Banner

```
Create a terminal-styled banner for echidnabot.

CONCEPT:
Make the banner look like a terminal window showing echidnabot running.

ELEMENTS:
- Terminal window frame (dark, with red/yellow/green dots)
- Inside the terminal:
  $ echidnabot verify --all

  ✓ src/proofs/theorem.v    [Coq]     verified
  ✓ src/specs/lemma.lean    [Lean4]   verified
  ✓ src/formal/prop.agda    [Agda]    verified

  All proofs verified in 3.2s

- Monospace font throughout
- Green checkmarks, cyan text
- Dark terminal background

This creates an immediate visual understanding of what the tool does.
```

---

## Favicon

```
Create a favicon for echidnabot.

DIMENSIONS: 32x32, 16x16 (provide both)

DESIGN:
- Extremely simplified echidna head silhouette
- Or: Just the "spines" as abstract triangular shapes
- Or: Turnstile symbol (⊢) with a tiny gear
- Must be recognizable at 16x16

COLORS:
- Electric cyan (#00d9ff) on transparent
- OR deep indigo background with cyan icon

Keep it VERY simple - almost iconic.
```

---

## Usage Notes

### Where to Apply

| Asset | Dimensions | Platform |
|-------|------------|----------|
| Avatar | 512x512 | GitHub org, GitLab group, npm, crates.io |
| Social Preview | 1280x640 | GitHub repo settings |
| Banner | 1500x500 | Twitter/X, LinkedIn |
| Favicon | 32x32, 16x16 | Docs site, web dashboard |

### File Formats

- **Avatar:** PNG with transparency, SVG preferred
- **Banner:** PNG (no transparency needed)
- **Favicon:** ICO (multi-size), PNG, SVG

### Accessibility

- Ensure sufficient contrast ratios (WCAG AA minimum)
- Provide alt text: "echidnabot logo - geometric echidna with mathematical symbols"
- Test visibility in both light and dark contexts

---

## Brand Voice

**Tone:** Technical, precise, confident, slightly witty

**Taglines (choose one or rotate):**
- "Proof-Aware CI"
- "Verify. Every. Commit."
- "Mathematical Certainty for Your Codebase"
- "Where Formal Methods Meet DevOps"
- "CI for Proof-Carrying Code"

**Avoid:**
- Marketing hyperbole ("revolutionary", "game-changing")
- Cutesy language or excessive exclamation points
- Claims we can't back up technically

---

*This branding guide is part of the echidnabot project.*
*SPDX-License-Identifier: PMPL-1.0-or-later
