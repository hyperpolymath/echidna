// SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-License-Identifier: MPL-2.0

//! `hyperpolymath_estate` corpus profile.
//!
//! A *profile* is a multi-repository manifest: it says which trees the
//! estate cares about, which adapter indexes each one, and which layer
//! of the stack that tree belongs to. The profile adapter runs the
//! existing per-format adapters over each entry and merges the results
//! into a single [`Corpus`], tagging every module with its repo and
//! layer.
//!
//! Why this exists: ECHIDNA's own lemmas should be in the index before
//! anyone else's. The ABI layer (Idris 2, `src/abi/` across repos) and
//! the type-theory libraries (Agda: `echo-types`, `epistemic-types`,
//! `secret-types`, `tropical-types`, `choreographic-types`) are the
//! material the estate actually proves things about, and no
//! single-repository adapter can see them.
//!
//! ## Manifest
//!
//! Read from `data/corpus-profiles/hyperpolymath-estate.toml` (or the
//! path in `ECHIDNA_ESTATE_MANIFEST`); [`Manifest::builtin`] is the
//! fallback so the adapter still works from any working directory.
//!
//! A `repo` entry with `name = "*"` matches every immediate child
//! directory of the root, which is how "`.idr` under `src/abi`,
//! whatever the repo" is expressed.
//!
//! ## Merging
//!
//! Each sub-corpus is indexed by its own adapter (so its hazard detection
//! and discipline tags are the real ones), then merged: module names gain
//! a `repo::` prefix, module options gain `repo:<name>` and
//! `layer:<layer>`, and entry qualified names keep the same prefix so
//! `by_qualified` stays unique across repos. Dependencies stay as bare
//! local names, which means a symbol named in two repos resolves across
//! them — useful for the "same concept, two proofs" case, at the cost of
//! not distinguishing the two in `dependencies` (see
//! `docs/CORPUS-ADAPTERS.adoc`).

#![allow(dead_code)]

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use serde::Deserialize;

use super::Corpus;

/// Adapter name as it appears in `corpus ingest --adapter`.
pub const PROFILE_NAME: &str = "hyperpolymath_estate";

/// Manifest location, relative to the repository root.
pub const DEFAULT_MANIFEST: &str = "data/corpus-profiles/hyperpolymath-estate.toml";

/// Environment override, mostly for tests and for out-of-tree runs.
pub const MANIFEST_ENV: &str = "ECHIDNA_ESTATE_MANIFEST";

#[derive(Debug, Clone, Deserialize)]
pub struct Manifest {
    pub profile: ProfileMeta,
    #[serde(default)]
    pub repo: Vec<RepoRule>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct ProfileMeta {
    pub name: String,
    #[serde(default)]
    pub description: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct RepoRule {
    /// Repository directory name, or `"*"` for every child directory.
    pub name: String,
    /// Paths inside the repository. Empty means the repository root.
    #[serde(default)]
    pub paths: Vec<String>,
    /// Which adapter indexes these paths.
    pub adapter: String,
    /// Estate layer label recorded on each module.
    #[serde(default)]
    pub layer: String,
}

impl Manifest {
    /// The manifest the repository ships, as code. Kept in step with
    /// `data/corpus-profiles/hyperpolymath-estate.toml`; a unit test
    /// asserts the two agree.
    pub fn builtin() -> Manifest {
        Manifest {
            profile: ProfileMeta {
                name: PROFILE_NAME.to_string(),
                description: "Idris2 ABI trees plus the five Agda type libraries".to_string(),
            },
            repo: vec![
                RepoRule {
                    name: "*".to_string(),
                    paths: vec!["src/abi".to_string()],
                    adapter: "idris2".to_string(),
                    layer: "abi".to_string(),
                },
                agda_repo("echo-types", "echo"),
                agda_repo("epistemic-types", "epistemic"),
                agda_repo("secret-types", "secret"),
                agda_repo("tropical-types", "tropical"),
                agda_repo("choreographic-types", "choreographic"),
            ],
        }
    }
}

fn agda_repo(repo: &str, layer: &str) -> RepoRule {
    RepoRule {
        name: repo.to_string(),
        paths: vec!["src".to_string(), String::new()],
        adapter: "agda".to_string(),
        layer: layer.to_string(),
    }
}

/// Load a manifest from `path`.
pub fn load_manifest(path: &Path) -> Result<Manifest> {
    let raw = std::fs::read_to_string(path)
        .with_context(|| format!("read corpus profile {}", path.display()))?;
    let manifest: Manifest =
        toml::from_str(&raw).with_context(|| format!("parse corpus profile {}", path.display()))?;
    Ok(manifest)
}

/// Locate the manifest: environment override, then the root, then the
/// working directory.
fn manifest_path(root: &Path) -> Option<PathBuf> {
    if let Some(p) = std::env::var_os(MANIFEST_ENV) {
        let p = PathBuf::from(p);
        if p.is_file() {
            return Some(p);
        }
    }
    let from_root = root.join(DEFAULT_MANIFEST);
    if from_root.is_file() {
        return Some(from_root);
    }
    if let Ok(cwd) = std::env::current_dir() {
        let from_cwd = cwd.join(DEFAULT_MANIFEST);
        if from_cwd.is_file() {
            return Some(from_cwd);
        }
    }
    None
}

/// Ingest the estate rooted at `root` (the directory containing the
/// repositories) using the shipped manifest when it can be found.
pub fn ingest(root: &Path) -> Result<Corpus> {
    let manifest = match manifest_path(root) {
        Some(p) => load_manifest(&p)?,
        None => Manifest::builtin(),
    };
    ingest_with_manifest(root, &manifest)
}

/// Ingest using an explicit manifest. `root` is the directory that
/// contains the repositories; a rule may also match `root` itself when
/// its name equals the root's basename.
pub fn ingest_with_manifest(root: &Path, manifest: &Manifest) -> Result<Corpus> {
    let mut corpus = Corpus {
        root: root.to_path_buf(),
        adapter: PROFILE_NAME.to_string(),
        ..Default::default()
    };

    // The same (adapter, directory) pair can be matched by more than one
    // rule (`*` plus a named repo whose layer is also interesting).
    let mut seen: HashSet<(String, PathBuf)> = HashSet::new();

    for rule in &manifest.repo {
        let repos = repo_dirs(root, &rule.name);
        for repo_dir in repos {
            let repo_name = repo_dir
                .file_name()
                .map(|s| s.to_string_lossy().into_owned())
                .unwrap_or_else(|| rule.name.clone());
            let bases = if rule.paths.is_empty() {
                vec![repo_dir.clone()]
            } else {
                rule.paths
                    .iter()
                    .map(|p| {
                        if p.is_empty() {
                            repo_dir.clone()
                        } else {
                            repo_dir.join(p)
                        }
                    })
                    .collect()
            };
            for base in bases {
                if !base.is_dir() {
                    continue;
                }
                let key = (rule.adapter.clone(), base.clone());
                if !seen.insert(key) {
                    continue;
                }
                let sub = ingest_dir(&rule.adapter, &base)?;
                merge_subcorpus(&mut corpus, sub, &repo_name, &rule.layer);
            }
        }
    }

    // Sub-corpora were already indexed (including discipline detection by
    // their own adapter), so only the link maps need rebuilding.
    corpus.reindex_links();
    Ok(corpus)
}

/// Immediate child directories of `root` for `name == "*"`, otherwise the
/// named repository (either `root/<name>` or `root` itself).
fn repo_dirs(root: &Path, name: &str) -> Vec<PathBuf> {
    if name == "*" {
        let mut out: Vec<PathBuf> = Vec::new();
        if let Ok(read) = std::fs::read_dir(root) {
            for entry in read.flatten() {
                let p = entry.path();
                if !p.is_dir() {
                    continue;
                }
                let file_name = entry.file_name().to_string_lossy().into_owned();
                if file_name.starts_with('.')
                    || matches!(file_name.as_str(), "target" | "node_modules" | "build")
                {
                    continue;
                }
                out.push(p);
            }
        }
        out.sort();
        out
    } else {
        let mut out: Vec<PathBuf> = Vec::new();
        let direct = root.join(name);
        if direct.is_dir() {
            out.push(direct);
        }
        let root_is_named = root
            .file_name()
            .map(|f| f.to_string_lossy().into_owned() == name)
            .unwrap_or(false);
        if root_is_named {
            out.push(root.to_path_buf());
        }
        out
    }
}

fn ingest_dir(adapter: &str, dir: &Path) -> Result<Corpus> {
    let corpus = match adapter {
        "agda" => super::agda::ingest(dir),
        "idris2" | "idris" => super::idris2::ingest(dir),
        "coq" => super::coq::ingest(dir),
        "lean" | "lean4" => super::lean::ingest(dir),
        "spark_ada" | "spark" | "ada" => super::spark_ada::ingest(dir),
        "creusot" | "rust_creusot" => super::creusot::ingest(dir),
        other => Err(anyhow::anyhow!(
            "profile rule uses unknown adapter '{}' (supported: agda, idris2, coq, lean, spark_ada, creusot)",
            other
        )),
    };
    corpus.with_context(|| format!("{} ingest of {}", adapter, dir.display()))
}

/// Merge `sub` into `dst`, prefixing module and entry names with the
/// repository and recording the estate layer on each module.
fn merge_subcorpus(dst: &mut Corpus, sub: Corpus, repo: &str, layer: &str) {
    let entry_offset = dst.entries.len();
    let module_offset = dst.modules.len();

    for mut module in sub.modules {
        module.name = format!("{}::{}", repo, module.name);
        module.options.push(format!("repo:{}", repo));
        if !layer.is_empty() {
            module.options.push(format!("layer:{}", layer));
        }
        for idx in module.entries.iter_mut() {
            *idx += entry_offset;
        }
        dst.modules.push(module);
    }

    for mut entry in sub.entries {
        entry.module_idx += module_offset;
        entry.qualified = format!("{}::{}", repo, entry.qualified);
        dst.entries.push(entry);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    fn write(path: &Path, body: &str) {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(path, body).unwrap();
    }

    #[test]
    fn builtin_manifest_covers_the_estate() {
        let m = Manifest::builtin();
        assert_eq!(m.profile.name, PROFILE_NAME);
        let names: Vec<&str> = m.repo.iter().map(|r| r.name.as_str()).collect();
        assert!(names.contains(&"*"), "wildcard ABI rule missing: {names:?}");
        for repo in [
            "echo-types",
            "epistemic-types",
            "secret-types",
            "tropical-types",
            "choreographic-types",
        ] {
            assert!(names.contains(&repo), "{repo} missing from {names:?}");
        }
        let abi = m.repo.iter().find(|r| r.name == "*").unwrap();
        assert_eq!(abi.adapter, "idris2");
        assert_eq!(abi.paths, vec!["src/abi".to_string()]);
        assert_eq!(abi.layer, "abi");
    }

    #[test]
    fn manifest_file_matches_builtin() {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(DEFAULT_MANIFEST);
        let from_disk = load_manifest(&path).expect("shipped manifest must parse");
        let builtin = Manifest::builtin();
        assert_eq!(from_disk.profile.name, builtin.profile.name);
        assert_eq!(from_disk.repo.len(), builtin.repo.len());
        for (disk, mem) in from_disk.repo.iter().zip(builtin.repo.iter()) {
            assert_eq!(disk.name, mem.name);
            assert_eq!(disk.adapter, mem.adapter);
            assert_eq!(disk.layer, mem.layer);
        }
    }

    #[test]
    fn rules_resolve_repositories_on_disk() {
        // A named rule matches the checkout when it is called that, and a
        // subdirectory of that name; the wildcard skips dotfiles and build
        // output. Built here rather than read from the checkout so the test
        // does not depend on what the clone directory happens to be called.
        let tmp = tempfile::tempdir().unwrap();
        let root = tmp.path().join("echidna");
        std::fs::create_dir_all(root.join("echo-types")).unwrap();
        std::fs::create_dir_all(root.join(".git")).unwrap();
        std::fs::create_dir_all(root.join("target")).unwrap();

        assert_eq!(repo_dirs(&root, "echidna"), vec![root.clone()]);
        assert_eq!(
            repo_dirs(&root, "echo-types"),
            vec![root.join("echo-types")]
        );

        let wildcard = repo_dirs(&root, "*");
        assert_eq!(
            wildcard,
            vec![root.join("echo-types")],
            "only real, non-build directories"
        );
        assert!(wildcard.iter().all(|d| d.is_dir()));
    }

    #[test]
    fn estate_sources_merge_into_one_corpus() {
        let tmp = tempfile::tempdir().unwrap();
        let root = tmp.path();

        // An ABI tree indexed by the idris2 adapter.
        write(
            &root.join("alpha/src/abi/Layout.idr"),
            "module ABI.Layout\n\n%default total\n\nexport\nlayoutBytes : Nat -> Nat\nlayoutBytes n = n\n",
        );
        // An Agda library indexed by the agda adapter.
        write(
            &root.join("echo-types/src/Echo.agda"),
            "module Echo where\n\ndata Unit : Set where\n  tt : Unit\n",
        );

        let corpus = ingest_with_manifest(root, &Manifest::builtin()).unwrap();
        assert_eq!(corpus.adapter, PROFILE_NAME);

        let modules: Vec<&str> = corpus.modules.iter().map(|m| m.name.as_str()).collect();
        assert!(
            modules.iter().any(|m| m.starts_with("alpha::")),
            "idris2 module missing: {modules:?}"
        );
        assert!(
            modules.iter().any(|m| m.starts_with("echo-types::")),
            "agda module missing: {modules:?}"
        );

        let abi = corpus
            .modules
            .iter()
            .find(|m| m.name.starts_with("alpha::"))
            .unwrap();
        assert!(abi.options.iter().any(|o| o == "repo:alpha"));
        assert!(abi.options.iter().any(|o| o == "layer:abi"));

        let echo = corpus
            .modules
            .iter()
            .find(|m| m.name.starts_with("echo-types::"))
            .unwrap();
        assert!(echo.options.iter().any(|o| o == "layer:echo"));

        assert!(!corpus.entries.is_empty(), "merged corpus has no entries");
        assert!(!corpus.by_qualified.is_empty());
    }

    #[test]
    fn entry_indices_stay_consistent_after_merge() {
        let tmp = tempfile::tempdir().unwrap();
        let root = tmp.path();
        write(
            &root.join("alpha/src/abi/Layout.idr"),
            "module ABI.Layout\n\nexport\nlayoutBytes : Nat -> Nat\nlayoutBytes n = n\n",
        );
        write(
            &root.join("beta/src/abi/Types.idr"),
            "module ABI.Types\n\nexport\nWord : Type\nWord = Nat\n",
        );
        let corpus = ingest_with_manifest(root, &Manifest::builtin()).unwrap();
        for (mi, module) in corpus.modules.iter().enumerate() {
            for &idx in &module.entries {
                assert!(idx < corpus.entries.len(), "dangling entry index {idx}");
                assert_eq!(corpus.entries[idx].module_idx, mi);
            }
        }
        for (qualified, &idx) in &corpus.by_qualified {
            assert_eq!(&corpus.entries[idx].qualified, qualified);
        }
    }

    #[test]
    fn unknown_adapter_in_manifest_is_an_error() {
        let tmp = tempfile::tempdir().unwrap();
        let root = tmp.path();
        write(&root.join("alpha/src/abi/A.idr"), "module A\n");
        let manifest = Manifest {
            profile: ProfileMeta {
                name: "test".to_string(),
                description: String::new(),
            },
            repo: vec![RepoRule {
                name: "*".to_string(),
                paths: vec!["src/abi".to_string()],
                adapter: "not_a_real_adapter".to_string(),
                layer: "abi".to_string(),
            }],
        };
        let err = ingest_with_manifest(root, &manifest).unwrap_err();
        let msg = format!("{err:#}");
        assert!(msg.contains("not_a_real_adapter"), "unexpected: {msg}");
    }

    #[test]
    fn empty_root_is_an_empty_corpus() {
        let tmp = tempfile::tempdir().unwrap();
        let corpus = ingest(tmp.path()).unwrap();
        assert_eq!(corpus.adapter, PROFILE_NAME);
        assert!(corpus.modules.is_empty());
        assert!(corpus.entries.is_empty());
    }

    #[test]
    fn explicit_manifest_is_honoured() {
        let tmp = tempfile::tempdir().unwrap();
        let root = tmp.path();
        write(&root.join("solo/src/abi/Only.idr"), "module Only\n");
        let manifest = Manifest {
            profile: ProfileMeta {
                name: "solo".to_string(),
                description: String::new(),
            },
            repo: vec![RepoRule {
                name: "solo".to_string(),
                paths: vec!["src/abi".to_string()],
                adapter: "idris2".to_string(),
                layer: "abi".to_string(),
            }],
        };
        let corpus = ingest_with_manifest(root, &manifest).unwrap();
        assert_eq!(corpus.modules.len(), 1);
        assert!(corpus.modules[0].name.starts_with("solo::"));
    }
}
