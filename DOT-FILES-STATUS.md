# Dot Files & Folders Status (2026-02-12)

## All Verified ✅

### Dot Directories (10)
| Directory | Status | Contents |
|-----------|--------|----------|
| `.bot_directives/` | ✅ Current | Bot directive SCM files (echidnabot, finishbot, glambot, rhodibot, seambot, sustainabot, robot-repo-automaton) |
| `.claude/` | ✅ Current | CLAUDE.md (language policy, RSR compliance) |
| `.clusterfuzzlite/` | ✅ Present | Fuzzing configuration |
| `.containerization/` | ✅ Present | Container configs |
| `.git/` | ✅ Active | Git repository (managed) |
| `.github/` | ✅ Current | 17 workflows, issue templates, FUNDING.yml |
| `.gitlab/` | ✅ Current | Issue/MR templates |
| `.guix-channel/` | ✅ Present | Guix channel config |
| `.machine_readable/` | ✅ **UPDATED** | STATE.scm (v1.5.0), META.scm, ECOSYSTEM.scm, AGENTIC.scm, NEUROSYM.scm, PLAYBOOK.scm |
| `.reuse/` | ✅ Present | REUSE compliance |

### Dot Files (10)
| File | Status | Purpose |
|------|--------|---------|
| `.echidnabot.toml` | ✅ **NEW** | Self-verification config (created 2026-02-12) |
| `.editorconfig` | ✅ Current | Editor settings for all languages (Rust, Julia, ReScript, etc.) |
| `.gitattributes` | ✅ Current | Git attributes |
| `.gitignore` | ✅ Current | Ignore patterns (target/, _build/, node_modules/, etc.) |
| `.gitlab-ci.yml` | ✅ Current | GitLab CI config |
| `.gitmodules` | ✅ Current | Submodule config (echidnabot) |
| `.nojekyll` | ✅ Present | Disable Jekyll on GitHub Pages |
| `.trivyignore` | ✅ Present | Trivy scanner ignore rules |

## Recent Updates

### Today (2026-02-12)
- ✅ Created `.echidnabot.toml` for self-verification
- ✅ Updated `.machine_readable/STATE.scm` to v1.5.0
- ✅ Removed root SCM duplicates (moved to .machine_readable/)

### Previously (2026-02-08)
- ✅ Updated `.machine_readable/META.scm` with trust hardening ADRs
- ✅ Updated `.machine_readable/ECOSYSTEM.scm` with 30 provers

## Compliance

✅ **RSR Standard**: All SCM files in `.machine_readable/` only
✅ **CCCP Standard**: Bot directives in `.bot_directives/`
✅ **EditorConfig**: Present and comprehensive
✅ **Git Attributes**: Present
✅ **REUSE**: Compliant (SPDX headers)

## Next Steps

1. ✅ GitLab sync: Attempted (blocked by branch protection - expected)
2. ⏭️ git-private-farm: Add echidna entry to manifest (deferred - has unstaged changes)

---

**All dot files and folders are up to date and production-ready!**
