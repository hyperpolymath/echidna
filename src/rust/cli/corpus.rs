// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! `echidna` CLI: corpus. Moved verbatim from main.rs (hotspot split).

use super::*;
use crate::output::OutputFormatter;
use anyhow::{Context, Result};
use echidna::ProverKind;
use std::path::PathBuf;

/// Corpus command - ingest, query, or summarise a project corpus.
///
/// First adapter is `agda`, targeted at echo-types' Buchholz / Brouwer
/// proof tree. Build the index once with `corpus ingest --root …`,
/// then query it without re-walking the source. The index is plain
/// JSON at `data/corpus/<basename>.json` so other tools (suggest, the
/// upcoming SA design search) can consume it directly.
///
/// Crossquery prints exact semantic-class and canonical-name matches from
/// per-prover tables and, unless `provers_only` is set, cross-prover dictionaries.
/// Identity queries skip declarations whose canonical keys are incomplete
/// and report the number skipped; only complete keys form identity groups.
///
/// # Errors
///
/// Returns an error for an unknown ingest adapter and propagates errors from
/// corpus ingestion, index or dictionary loading, export/import, saving and
/// output formatting. Resolving a default index can also fail if the working
/// directory cannot be obtained. Queries with no matches succeed.
pub(crate) fn corpus_command(op: CorpusOp, formatter: &OutputFormatter) -> Result<()> {
    use echidna::corpus::{self, Corpus};

    let default_index = |root_basename: &str| -> PathBuf {
        PathBuf::from("data/corpus").join(format!("{}.json", root_basename))
    };

    match op {
        CorpusOp::Ingest { root, adapter, out } => {
            let root = root.canonicalize().unwrap_or(root);
            let basename = root
                .file_name()
                .map(|s| s.to_string_lossy().into_owned())
                .unwrap_or_else(|| "project".to_string());
            let out = out.unwrap_or_else(|| default_index(&basename));

            let corpus = match adapter.as_str() {
                "agda" => corpus::agda::ingest(&root)
                    .with_context(|| format!("agda ingest of {}", root.display()))?,
                "coq" => corpus::coq::ingest(&root)
                    .with_context(|| format!("coq ingest of {}", root.display()))?,
                "lean" | "lean4" => corpus::lean::ingest(&root)
                    .with_context(|| format!("lean ingest of {}", root.display()))?,
                "idris2" | "idris" => corpus::idris2::ingest(&root)
                    .with_context(|| format!("idris2 ingest of {}", root.display()))?,
                "acl2_books" => corpus::acl2_books::ingest(&root)
                    .with_context(|| format!("acl2_books ingest of {}", root.display()))?,
                "dafny" => corpus::dafny::ingest(&root)
                    .with_context(|| format!("dafny ingest of {}", root.display()))?,
                "spark_ada" | "spark" | "ada" => corpus::spark_ada::ingest(&root)
                    .with_context(|| format!("spark_ada ingest of {}", root.display()))?,
                "creusot" | "rust_creusot" => corpus::creusot::ingest(&root)
                    .with_context(|| format!("creusot ingest of {}", root.display()))?,
                "hyperpolymath_estate" | "estate" => corpus::profile::ingest(&root)
                    .with_context(|| format!("estate profile ingest of {}", root.display()))?,
                "fstar" => corpus::fstar::ingest(&root)
                    .with_context(|| format!("fstar ingest of {}", root.display()))?,
                "hol4" => corpus::hol4::ingest(&root)
                    .with_context(|| format!("hol4 ingest of {}", root.display()))?,
                "hol_light" => corpus::hol_light::ingest(&root)
                    .with_context(|| format!("hol_light ingest of {}", root.display()))?,
                "isabelle" => corpus::isabelle::ingest(&root)
                    .with_context(|| format!("isabelle ingest of {}", root.display()))?,
                "metamath" => corpus::metamath::ingest(&root)
                    .with_context(|| format!("metamath ingest of {}", root.display()))?,
                "minif2f" => corpus::minif2f::ingest(&root)
                    .with_context(|| format!("minif2f ingest of {}", root.display()))?,
                "mizar" => corpus::mizar::ingest(&root)
                    .with_context(|| format!("mizar ingest of {}", root.display()))?,
                "proofnet" => corpus::proofnet::ingest(&root)
                    .with_context(|| format!("proofnet ingest of {}", root.display()))?,
                "smtlib" => corpus::smtlib::ingest(&root)
                    .with_context(|| format!("smtlib ingest of {}", root.display()))?,
                "tptp" => corpus::tptp::ingest(&root)
                    .with_context(|| format!("tptp ingest of {}", root.display()))?,
                "why3" => corpus::why3::ingest(&root)
                    .with_context(|| format!("why3 ingest of {}", root.display()))?,
                other => {
                    return Err(anyhow::anyhow!(
                        "Unknown corpus adapter '{}' (supported: agda, coq, lean, idris2, acl2_books, creusot, dafny, fstar, hol4, hol_light, isabelle, metamath, minif2f, mizar, proofnet, smtlib, spark_ada, tptp, why3, hyperpolymath_estate)",
                        other
                    ))
                },
            };
            corpus.save_json(&out)?;
            let stats = corpus.stats();
            formatter.info(&format!(
                "ingested {} module(s), {} entry/-ies ({} fn, {} data, {} record, {} postulate); {} entry/-ies have hazards; index: {}",
                stats.modules,
                stats.entries,
                stats.functions,
                stats.data,
                stats.records,
                stats.postulates,
                stats.with_hazards,
                out.display()
            ))?;
        },
        CorpusOp::Query {
            pattern,
            index,
            deps,
            reverse_deps,
            reverse_closure,
        } => {
            let path = match index {
                Some(p) => p,
                None => {
                    let basename = std::env::current_dir()?
                        .file_name()
                        .map(|s| s.to_string_lossy().into_owned())
                        .unwrap_or_else(|| "project".to_string());
                    default_index(&basename)
                },
            };
            let corpus = Corpus::load_json(&path)
                .with_context(|| format!("load corpus index {}", path.display()))?;
            let hits = corpus.find(&pattern);
            if hits.is_empty() {
                formatter.info(&format!("no matches for '{}'", pattern))?;
                return Ok(());
            }
            for entry in &hits {
                let module = corpus
                    .modules
                    .get(entry.module_idx)
                    .map(|m| m.name.as_str())
                    .unwrap_or("?");
                println!(
                    "{}  [{:?}] {}:{}",
                    entry.qualified, entry.kind, module, entry.line
                );
                println!("  : {}", entry.statement);
                if entry.axiom_usage.any() {
                    println!("  ⚠ hazards: {:?}", entry.axiom_usage);
                }
                if !entry.dependencies.is_empty() {
                    let mut deps_list = entry.dependencies.clone();
                    deps_list.sort();
                    println!("  deps ({}): {}", deps_list.len(), deps_list.join(", "));
                }
            }
            if deps && hits.len() == 1 {
                let closure = corpus.closure(&hits[0].qualified);
                println!("\ntransitive closure ({} entries):", closure.len());
                let mut names: Vec<&str> = closure.iter().map(|e| e.qualified.as_str()).collect();
                names.sort();
                for n in names {
                    println!("  {}", n);
                }
            }
            if reverse_deps && hits.len() == 1 {
                let rev = corpus.reverse_deps(&hits[0].qualified);
                println!(
                    "\ndirect reverse-deps of {} ({} entries):",
                    hits[0].qualified,
                    rev.len()
                );
                let mut names: Vec<&str> = rev.iter().map(|e| e.qualified.as_str()).collect();
                names.sort();
                for n in names {
                    println!("  {}", n);
                }
            }
            if reverse_closure && hits.len() == 1 {
                let closure = corpus.reverse_closure(&hits[0].qualified);
                println!(
                    "\nreverse closure (impact set) of {} ({} entries):",
                    hits[0].qualified,
                    closure.len()
                );
                let mut names: Vec<&str> = closure.iter().map(|e| e.qualified.as_str()).collect();
                names.sort();
                for n in names {
                    println!("  {}", n);
                }
            }
        },
        CorpusOp::Crossquery {
            class,
            synonyms_dir,
            provers_only,
        } => {
            use echidna::suggest::synonyms::{
                load_all, load_cross_prover_dicts, SynonymEntry, SynonymTable,
            };
            let dir = synonyms_dir.unwrap_or_else(|| PathBuf::from("data/synonyms"));
            let tables = load_all(&dir)
                .with_context(|| format!("load synonym tables from {}", dir.display()))?;
            // Prints the hits in `table` for `class` and returns how many.
            // A row whose canonical name *is* `class` also counts: the MSC
            // dictionary is keyed by code, so `crossquery 68Q60` should find
            // 68Q60 even though its semantic class is `program-specification`.
            let print_hits = |table: &SynonymTable, label: std::fmt::Arguments<'_>| -> usize {
                let mut hits: Vec<&SynonymEntry> = table.by_semantic_class(&class);
                if let Some(entry) = table.entries.iter().find(|e| e.canonical == class) {
                    if !hits.iter().any(|h| h.canonical == entry.canonical) {
                        hits.push(entry);
                    }
                }
                if hits.is_empty() {
                    return 0;
                }
                println!("{label}:");
                for entry in &hits {
                    let aliases = if entry.aliases.is_empty() {
                        String::new()
                    } else {
                        format!(" (aliases: {})", entry.aliases.join(", "))
                    };
                    println!("  {}{}", entry.canonical, aliases);
                }
                hits.len()
            };
            let mut total = 0usize;
            let mut sources = 0usize;
            for prover in [
                ProverKind::Agda,
                ProverKind::Coq,
                ProverKind::Lean,
                ProverKind::Idris2,
                ProverKind::Isabelle,
                ProverKind::Metamath,
                ProverKind::Mizar,
                ProverKind::HOL4,
                ProverKind::HOLLight,
                ProverKind::Dafny,
                ProverKind::Why3,
                ProverKind::FStar,
                ProverKind::ACL2,
            ] {
                if let Some(table) = tables.get(&prover) {
                    let hits = print_hits(table, format_args!("{:?}", prover));
                    total += hits;
                    if hits > 0 {
                        sources += 1;
                    }
                }
            }
            if !provers_only {
                let dicts = load_cross_prover_dicts(&dir).with_context(|| {
                    format!("load cross-prover dictionaries from {}", dir.display())
                })?;
                for (name, table) in dicts.tables() {
                    let hits = print_hits(table, format_args!("dictionary {}", name));
                    total += hits;
                    if hits > 0 {
                        sources += 1;
                    }
                }
            }
            if total == 0 {
                formatter.info(&format!("no entries for semantic class '{}'", class))?;
            } else {
                formatter.info(&format!(
                    "{} entries across {} table(s) for semantic class '{}'",
                    total, sources, class
                ))?;
            }
        },

        CorpusOp::Near { query, index, top } => {
            let path = match index {
                Some(p) => p,
                None => {
                    let basename = std::env::current_dir()?
                        .file_name()
                        .map(|s| s.to_string_lossy().into_owned())
                        .unwrap_or_else(|| "project".to_string());
                    default_index(&basename)
                },
            };
            let corpus = Corpus::load_json(&path)
                .with_context(|| format!("load corpus index {}", path.display()))?;
            let q_vec = corpus.embed_query(&query);
            let nn = corpus.nearest_neighbours(&q_vec, top);
            if nn.is_empty() {
                formatter.info(&format!(
                    "no entries near '{}' (corpus has {} entries)",
                    query,
                    corpus.entries.len()
                ))?;
                return Ok(());
            }
            for (idx, sim) in &nn {
                let entry = &corpus.entries[*idx];
                println!("{:.3}  {}  [{:?}]", sim, entry.qualified, entry.kind);
                println!("       : {}", entry.statement);
            }
        },

        CorpusOp::Identity {
            pattern,
            index,
            skeleton,
            cross_only,
        } => {
            let path = match index {
                Some(p) => p,
                None => {
                    let basename = std::env::current_dir()?
                        .file_name()
                        .map(|s| s.to_string_lossy().into_owned())
                        .unwrap_or_else(|| "project".to_string());
                    default_index(&basename)
                },
            };
            let corpus = Corpus::load_json(&path)
                .with_context(|| format!("load corpus index {}", path.display()))?;
            let needle = pattern.to_lowercase();
            let everything = needle == "*";

            // Group by structural key, keeping the key itself for display.
            let mut groups: std::collections::BTreeMap<
                String,
                (
                    echidna::corpus::canonical::StructuralKey,
                    Vec<(String, String)>,
                ),
            > = std::collections::BTreeMap::new();
            // A key the canonicaliser did not derive from the whole statement
            // is a shared prefix, not an identity (docs/CORPUS.adoc).
            let mut skipped_incomplete = 0usize;
            for entry in &corpus.entries {
                let matches = everything
                    || entry.qualified.to_lowercase().contains(&needle)
                    || entry.name.to_lowercase().contains(&needle);
                if !matches {
                    continue;
                }
                let key = echidna::corpus::canonical::structural_key(&entry.statement);
                if !key.complete {
                    skipped_incomplete += 1;
                    continue;
                }
                let slot = groups
                    .entry(key.key.clone())
                    .or_insert_with(|| (key, Vec::new()));
                slot.1
                    .push((corpus.adapter.clone(), entry.qualified.clone()));
            }

            if skipped_incomplete > 0 {
                formatter.info(&format!(
                    "{skipped_incomplete} matching declaration(s) skipped: the canonicaliser \
                     did not read their statement completely, so they carry no identity"
                ))?;
            }
            if groups.is_empty() {
                // When every match was skipped, the name is present but carries
                // no identity; saying "no declarations" would mislead.
                let what = if skipped_incomplete > 0 {
                    "no completely read declarations"
                } else {
                    "no declarations"
                };
                formatter.info(&format!("{what} matching '{}'", pattern))?;
                return Ok(());
            }

            let mut shown = 0usize;
            for (key, (structural, members)) in &groups {
                let adapters: std::collections::BTreeSet<&str> =
                    members.iter().map(|(a, _)| a.as_str()).collect();
                if cross_only && adapters.len() < 2 {
                    continue;
                }
                shown += 1;
                println!(
                    "{}  [{}] {} declaration(s) across {} adapter(s)",
                    &key[..16.min(key.len())],
                    structural.tier.as_str(),
                    members.len(),
                    adapters.len()
                );
                println!("  type: {}", structural.shape);
                if skeleton {
                    println!("  skeleton: {}", structural.skeleton);
                }
                for (adapter, qualified) in members {
                    println!("    {}  {}", adapter, qualified);
                }
            }
            formatter.info(&format!(
                "{} key(s) over {} declaration(s) in {}",
                shown,
                groups.values().map(|(_, m)| m.len()).sum::<usize>(),
                path.display()
            ))?;
        },

        CorpusOp::ExportOctads { index, out } => {
            let corpus = Corpus::load_json(&index)
                .with_context(|| format!("load corpus index {}", index.display()))?;
            let timestamp = chrono::Utc::now().to_rfc3339();
            corpus.save_octads_jsonl(&out, &timestamp)?;
            formatter.info(&format!(
                "exported {} octad(s) → {}",
                corpus.entries.len(),
                out.display()
            ))?;
        },

        CorpusOp::ImportOctads { octads, out } => {
            let corpus = Corpus::load_octads_jsonl(&octads)
                .with_context(|| format!("load octads {}", octads.display()))?;
            corpus.save_json(&out)?;
            formatter.info(&format!(
                "imported {} octad(s) ({} module(s)) → {}",
                corpus.entries.len(),
                corpus.modules.len(),
                out.display()
            ))?;
        },

        CorpusOp::Stats { index } => {
            let path = match index {
                Some(p) => p,
                None => {
                    let basename = std::env::current_dir()?
                        .file_name()
                        .map(|s| s.to_string_lossy().into_owned())
                        .unwrap_or_else(|| "project".to_string());
                    default_index(&basename)
                },
            };
            let corpus = Corpus::load_json(&path)
                .with_context(|| format!("load corpus index {}", path.display()))?;
            let stats = corpus.stats();
            println!(
                "modules:    {}\nentries:    {}\n  functions:  {}\n  data:       {}\n  records:    {}\n  postulates: {}\nwith hazards: {}\nwith deps:    {}",
                stats.modules,
                stats.entries,
                stats.functions,
                stats.data,
                stats.records,
                stats.postulates,
                stats.with_hazards,
                stats.with_deps
            );
        },
    }

    Ok(())
}
