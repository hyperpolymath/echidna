# echidnabot Release Checklist

Complete checklist for making echidnabot a perfect release.

## Repository Setup ✅

### Done
- [x] README.adoc - SEO-optimized, project-focused
- [x] BRANDING.md - Visual identity and LLM art prompts
- [x] justfile - RSR canonical task runner
- [x] Nickel configuration (config/echidnabot.ncl)
- [x] MCP configuration (.claude/settings/mcp.json)
- [x] STATE.scm - Project checkpoint
- [x] META.scm - Dublin Core metadata
- [x] ECOSYSTEM.scm - Dependency graph
- [x] GitHub topics file (.github/topics.txt)

### To Apply Manually
- [ ] **Apply GitHub Topics** - Go to repo Settings → About → Topics and add:
  ```
  theorem-prover, formal-verification, proof-assistant, ci-cd, rust, coq,
  lean4, agda, isabelle, z3, smt, formal-methods, type-theory, github-app,
  automation, mathematics, logic, webhooks, hacktoberfest
  ```
- [ ] **Update GitHub Description** - Set to:
  > Proof-aware CI bot that verifies mathematical theorems on every push. Coq, Lean, Agda, Isabelle, Z3 support. Rust + Tokio + GraphQL.

## Wiki ✅

### Done
- [x] wiki/Home.md
- [x] wiki/Getting-Started.md
- [x] wiki/Architecture.md
- [x] wiki/Supported-Provers.md
- [x] wiki/FAQ.md

### To Add
- [ ] wiki/Configuration-Reference.md - All config options
- [ ] wiki/API-Reference.md - GraphQL schema documentation
- [ ] wiki/Platform-Integration.md - GitHub/GitLab/Bitbucket setup
- [ ] wiki/Troubleshooting.md - Common issues
- [ ] wiki/Changelog.md - Version history
- [ ] wiki/Roadmap.md - Future plans

### To Do Manually
- [ ] **Enable Wiki** in GitHub repo settings
- [ ] **Push wiki/** to the wiki repo:
  ```bash
  git clone https://github.com/hyperpolymath/echidnabot.wiki.git
  cp wiki/*.md echidnabot.wiki/
  cd echidnabot.wiki && git add . && git commit -m "Initial wiki" && git push
  ```

## CI/CD ✅

### Done
- [x] .github/workflows/quality.yml - Rust build/test/lint
- [x] .github/workflows/docs.yml - casket-ssg documentation
- [x] .github/workflows/echidnabot.yml - Self-referential proof checking
- [x] .github/workflows/codeql.yml - Security scanning
- [x] .github/workflows/scorecard.yml - OSSF Scorecard

### To Add/Verify
- [ ] Ensure all workflows pass on main branch
- [ ] Add release workflow for crates.io publishing
- [ ] Add container publishing to ghcr.io

## Documentation 🔄

### Done
- [x] README.adoc
- [x] ARCHITECTURE.adoc (if present)
- [x] CONTRIBUTING.adoc
- [x] SECURITY.md
- [x] CODE_OF_CONDUCT.md

### To Add
- [ ] docs/DEPLOYMENT.md - Production deployment guide
- [ ] docs/CONFIGURATION.md - Detailed config reference
- [ ] Man pages (docs/man/echidnabot.1)

## Branding Assets 📝

### To Create (using LLM prompts in BRANDING.md)
- [ ] **Avatar** (512x512) - Geometric echidna logo
- [ ] **Banner** (1280x640) - GitHub social preview
- [ ] **Favicon** (32x32, 16x16) - For docs site

### To Apply
- [ ] Upload avatar to GitHub org/repo
- [ ] Set social preview image in repo settings
- [ ] Add favicon to docs site

## Code Quality 🔄

### To Complete
- [ ] Run `cargo fmt` on all files
- [ ] Run `cargo clippy` and fix all warnings
- [ ] Achieve 50%+ test coverage
- [ ] Add integration tests
- [ ] Run `cargo audit` and fix vulnerabilities
- [ ] Run `cargo deny check` for license compliance

## Core Functionality 🔄

### Phase 1 (MVP)
- [ ] GitHub webhook handler with signature verification
- [ ] Proof file detection (by extension)
- [ ] ECHIDNA Core dispatcher client
- [ ] GitHub Check Run reporter
- [ ] SQLite persistence
- [ ] CLI: serve, register, check, status

### Phase 2 (Multi-Prover)
- [ ] Auto-detect prover from file extension
- [ ] Support Coq, Lean 4, Agda, Z3
- [ ] Parallel proof checking
- [ ] Aggregated results

## Security ✅

### Done
- [x] SECURITY.md policy
- [x] .well-known/security.txt
- [x] HMAC-SHA256 webhook verification (code exists)
- [x] No hardcoded secrets
- [x] SHA-pinned GitHub Actions

### To Verify
- [ ] Run TruffleHog scan: no secrets in history
- [ ] Run CodeQL: no critical findings
- [ ] OSSF Scorecard: 7+ score

## Packaging 🔄

### Done
- [x] Cargo.toml metadata complete
- [x] guix.scm package definition
- [x] Containerfile for Docker/Podman
- [x] justfile for task automation

### To Add
- [ ] flake.nix for Nix users
- [ ] cargo-deb configuration
- [ ] cargo-rpm configuration
- [ ] Homebrew formula (optional)

## Release Process

### Pre-Release
1. [ ] All tests passing
2. [ ] Changelog updated
3. [ ] Version bumped in Cargo.toml
4. [ ] STATE.scm updated
5. [ ] Documentation reviewed

### Release
1. [ ] Create git tag: `git tag -s v0.1.0 -m "Release 0.1.0"`
2. [ ] Push tag: `git push origin v0.1.0`
3. [ ] GitHub release created with notes
4. [ ] Publish to crates.io: `cargo publish`
5. [ ] Container pushed to ghcr.io
6. [ ] Announce on relevant channels

### Post-Release
1. [ ] Verify crates.io page
2. [ ] Verify container works
3. [ ] Update roadmap
4. [ ] Start next milestone

## External Integration

### GitHub
- [ ] Enable GitHub Discussions
- [ ] Set up issue templates (if not present)
- [ ] Configure branch protection rules
- [ ] Enable Dependabot

### Marketing
- [ ] Post to Hacker News (when ready)
- [ ] Post to r/rust, r/programming
- [ ] Post to Coq, Lean, Agda communities
- [ ] Add to Awesome lists (awesome-rust, etc.)

## Metrics

### Success Criteria for v1.0
- [ ] 100+ GitHub stars
- [ ] 5+ external contributors
- [ ] 3+ production users
- [ ] 80%+ test coverage
- [ ] OSSF Scorecard 8+

---

## Priority Order

1. **Immediate** (before merge)
   - Apply GitHub topics manually
   - Update GitHub description
   - Enable wiki and push content

2. **This Week**
   - Create branding assets
   - Add missing wiki pages
   - Complete Phase 1 functionality

3. **This Month**
   - Achieve MVP release (v0.2)
   - 50% test coverage
   - flake.nix packaging

4. **Next Quarter**
   - v1.0 production release
   - Multi-platform support
   - ML tactic suggestions
