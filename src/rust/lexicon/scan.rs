// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! `echidna lexicon scan`: a cross-corpus candidate generator for the lexicon.
//!
//! Two corpora are compared along two axes, the *name* of a theorem and the
//! canonical *shape* of its statement ([`crate::corpus::canonical`], scheme
//! `dk-shape-v1`). The four combinations are the four things a curator
//! wants to know about:
//!
//! | | same shape | different shape |
//! |---|---|---|
//! | **same name** | cognate | false friend, or specialisation |
//! | **different name** | synonym candidate | unrelated (not reported) |
//!
//! A pair joined by name is classified by the strongest tier at which its two
//! statements agree: identical text (`cognate_exact`), the same structural
//! key (`cognate_shape`: same shape up to variable names), the same skeleton
//! key only (`cognate_skeleton`: the shapes differ in binders or sorts, the
//! usual signature of a specialisation such as `nat` against `real`), or
//! none (`differs`). A pair joined by identical text, by shape, or failing
//! those by skeleton has different names and is a synonym candidate; the
//! text join needs no canonicaliser at all.
//!
//! Shape classification needs both statements read *completely*
//! ([`StructuralKey::complete`]). `dk-shape-v1` still returns a
//! structural-tier key when its parser stops early or meets notation it has
//! no rule for (HOL binders, Isabelle `\<…>` escapes), and that key is a
//! prefix many different statements share. Such pairs are `unparsed`, and
//! such statements take no part in shape or skeleton joins.
//!
//! None of this is evidence. The canonical shape is a syntactic key, not a
//! decision procedure; `dk-shape-v1` documents what it does not normalise,
//! and [`Coverage`] measures how much of each corpus it actually reads and
//! how often distinct statements collide on one key. Every candidate is
//! written with `evidence = { kind = "none" }` and never edits
//! `data/synonyms/` (owner decision D4).
//!
//! Output is I-JSON serialised as JCS (RFC 8785), one record per line, so
//! records hash and diff stably. Each candidate's `id` is the UUIDv8 content
//! id ([`crate::ids::content_id`]) of the statement pair alone, with the two
//! sides in a fixed order: the same pair keeps the same id whichever corpus
//! is named first and whichever normaliser version classified it, so a
//! curator's review survives a re-scan.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs::{self, File};
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use anyhow::{bail, Context, Result};
use serde::Serialize;

use crate::corpus::canonical::{self, KeyTier, StructuralKey};
use crate::suggest::synonyms::LexiconEvidence;

/// Schema tag of one candidate record.
pub const CANDIDATE_SCHEMA: &str = "echidna.lexicon.candidate/1";
/// Schema tag of one per-pair summary record.
pub const PAIR_SUMMARY_SCHEMA: &str = "echidna.lexicon.pair-summary/1";
/// Schema tag of one per-corpus coverage record.
pub const COVERAGE_SCHEMA: &str = "echidna.lexicon.coverage/1";
/// Schema tag of one sampled key-collision group.
pub const COLLISION_SCHEMA: &str = "echidna.lexicon.collision/1";

/// One corpus per prover family, the cross-family spanning set: classical
/// higher-order logic (HOL4), Isabelle/HOL (the AFP), dependent type theory
/// (Lean 3), set theory (Mizar), first-order computational logic (ACL2),
/// auto-active verification (Why3), logic programming (λProlog) and the
/// λΠ-modulo hub (Dedukti).
pub const SPANNING: [&str; 8] = [
    "hol4",
    "afp",
    "lean3",
    "mizar",
    "acl2",
    "why3",
    "lambda_prolog",
    "dedukti",
];

/// One pair inside each family that has a second corpus, so differences
/// within a family can be told apart from differences across families.
pub const IN_FAMILY: [(&str, &str); 5] = [
    ("hol4", "hol_light"),
    ("lean3", "agda"),
    ("acl2", "acl2s"),
    ("why3", "dafny"),
    ("mizar", "isabelle_zf"),
];

/// The two pairs read first: the stage-6a pilot pair inside the HOL family,
/// and the cross-family pair with the most shared names.
pub const LEARNING: [(&str, &str); 2] = [("hol4", "hol_light"), ("lean3", "afp")];

/// The pairs a named preset expands to, in scan order, or `None` for an
/// unknown preset. `full` is every spanning pair followed by the in-family
/// pairs.
pub fn preset_pairs(preset: &str) -> Option<Vec<(String, String)>> {
    let owned = |pairs: &[(&str, &str)]| {
        pairs
            .iter()
            .map(|(a, b)| (a.to_string(), b.to_string()))
            .collect::<Vec<_>>()
    };
    let spanning = || {
        let mut out = Vec::new();
        for (i, a) in SPANNING.iter().enumerate() {
            for b in &SPANNING[i + 1..] {
                out.push((a.to_string(), b.to_string()));
            }
        }
        out
    };
    match preset {
        "learning" => Some(owned(&LEARNING)),
        "spanning" => Some(spanning()),
        "in-family" => Some(owned(&IN_FAMILY)),
        "full" => {
            let mut out = spanning();
            out.extend(owned(&IN_FAMILY));
            Some(out)
        },
        _ => None,
    }
}

/// Parse a `A:B` pair argument. Both sides must be corpus keys as they
/// appear in `proof_states_<key>.jsonl`.
pub fn parse_pair(arg: &str) -> Result<(String, String)> {
    let (a, b) = arg
        .split_once(':')
        .with_context(|| format!("pair `{arg}` must be written A:B"))?;
    validate_corpus_key(a)?;
    validate_corpus_key(b)?;
    if a == b {
        bail!("pair `{arg}` names the same corpus twice");
    }
    Ok((a.to_string(), b.to_string()))
}

/// Corpus keys become file names, so only `[a-z0-9_]` is accepted.
pub fn validate_corpus_key(key: &str) -> Result<()> {
    if key.is_empty()
        || !key
            .chars()
            .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_')
    {
        bail!("corpus key `{key}` must be non-empty [a-z0-9_]");
    }
    // `pairs/<a>__<b>.jsonl` is unambiguous only if no key contains `__`.
    if key.contains("__") {
        bail!("corpus key `{key}` must not contain `__`");
    }
    Ok(())
}

/// Fold a theorem name for cross-prover matching: keep the last component
/// of a dotted or `::`-qualified name, lower-case it, read `-` as `_`, and
/// trim surrounding underscores. `nat.add_comm`, `ADD_COMM` and `add-comm`
/// all fold to `add_comm`.
pub fn fold_name(name: &str) -> String {
    let tail = name.rsplit(['.', ':']).next().unwrap_or(name);
    let tail = if tail.is_empty() { name } else { tail };
    tail.to_lowercase()
        .replace('-', "_")
        .trim_matches('_')
        .to_string()
}

/// Folded names that say nothing about the statement: numbered lemmas,
/// examples, auxiliaries, Mizar's anonymous theorems and any stem of two
/// characters or fewer once trailing digits, primes and underscores are
/// removed (`l3`, `th27`, `ex1`, `z`).
const GENERIC_STEMS: [&str; 34] = [
    "anonymous",
    "aux",
    "auxiliary",
    "bar",
    "base",
    "baz",
    "case",
    "claim",
    "cor",
    "corollary",
    "def",
    "defn",
    "example",
    "exercise",
    "fact",
    "foo",
    "goal",
    "helper",
    "ind",
    "key",
    "lem",
    "lemma",
    "main",
    "prop",
    "remark",
    "result",
    "step",
    "sublemma",
    "temp",
    "test",
    "thm",
    "theorem",
    "tmp",
    "unnamed",
];

/// Whether a folded name is too generic to join two corpora on.
pub fn is_generic(folded: &str) -> bool {
    let stem = folded.trim_end_matches(|c: char| c.is_ascii_digit() || c == '\'' || c == '_');
    stem.chars().count() <= 2 || GENERIC_STEMS.contains(&stem)
}

/// One distinct `(name, statement)` row of a corpus.
#[derive(Debug, Clone)]
pub struct Entry {
    pub name: String,
    /// The statement with runs of whitespace collapsed to one space.
    pub statement: String,
    key: usize,
}

/// A training corpus, deduplicated and indexed for the scan.
#[derive(Debug, Clone)]
pub struct Corpus {
    pub key: String,
    /// Distinct rows, sorted by name then statement.
    pub entries: Vec<Entry>,
    keys: Vec<StructuralKey>,
    pub lines_read: usize,
    /// Lines that are not JSON objects.
    pub lines_malformed: usize,
    /// Objects without a non-empty string `theorem` and `goal`.
    pub lines_without_statement: usize,
    by_name: BTreeMap<String, Vec<usize>>,
    by_fold: BTreeMap<String, BTreeSet<String>>,
    by_statement: BTreeMap<String, Vec<usize>>,
    by_shape: BTreeMap<String, Vec<usize>>,
    by_skeleton: BTreeMap<String, Vec<usize>>,
}

fn collapse_whitespace(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

impl Corpus {
    /// Build a corpus from `(name, statement)` rows. Names are trimmed,
    /// statement whitespace is collapsed, and rows with an empty side or a
    /// duplicate of an earlier row are dropped.
    pub fn from_rows<I>(key: &str, rows: I) -> Self
    where
        I: IntoIterator<Item = (String, String)>,
    {
        let distinct: BTreeSet<(String, String)> = rows
            .into_iter()
            .map(|(n, s)| (n.trim().to_string(), collapse_whitespace(&s)))
            .filter(|(n, s)| !n.is_empty() && !s.is_empty())
            .collect();

        let mut keys: Vec<StructuralKey> = Vec::new();
        let mut key_of: HashMap<String, usize> = HashMap::new();
        let mut entries = Vec::with_capacity(distinct.len());
        for (name, statement) in distinct {
            let k = match key_of.get(&statement) {
                Some(&k) => k,
                None => {
                    keys.push(canonical::structural_key(&statement));
                    key_of.insert(statement.clone(), keys.len() - 1);
                    keys.len() - 1
                },
            };
            entries.push(Entry {
                name,
                statement,
                key: k,
            });
        }

        let mut by_name: BTreeMap<String, Vec<usize>> = BTreeMap::new();
        let mut by_fold: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        let mut by_shape: BTreeMap<String, Vec<usize>> = BTreeMap::new();
        let mut by_statement: BTreeMap<String, Vec<usize>> = BTreeMap::new();
        let mut by_skeleton: BTreeMap<String, Vec<usize>> = BTreeMap::new();
        for (i, e) in entries.iter().enumerate() {
            by_name.entry(e.name.clone()).or_default().push(i);
            by_statement.entry(e.statement.clone()).or_default().push(i);
            let folded = fold_name(&e.name);
            if !folded.is_empty() {
                by_fold.entry(folded).or_default().insert(e.name.clone());
            }
            // Only a complete parse can stand for its statement in a join;
            // an incomplete shape is a prefix that other statements share.
            let k = &keys[e.key];
            if !k.complete {
                continue;
            }
            if k.tier == KeyTier::Structural {
                by_shape.entry(k.key.clone()).or_default().push(i);
            }
            if !k.skeleton.is_empty() {
                by_skeleton
                    .entry(k.skeleton_key.clone())
                    .or_default()
                    .push(i);
            }
        }

        Corpus {
            key: key.to_string(),
            entries,
            keys,
            lines_read: 0,
            lines_malformed: 0,
            lines_without_statement: 0,
            by_name,
            by_statement,
            by_fold,
            by_shape,
            by_skeleton,
        }
    }

    /// Load `training_dir/proof_states_<key>.jsonl`, reading each line's
    /// `theorem` and `goal` strings.
    ///
    /// # Errors
    ///
    /// The key is not `[a-z0-9_]`, or the file is missing, unreadable, not
    /// UTF-8, or holds no usable row. Lines that are not JSON objects, or
    /// lack a string `theorem` or `goal`, are counted rather than fatal.
    pub fn load(training_dir: &Path, key: &str) -> Result<Self> {
        validate_corpus_key(key)?;
        let path = training_dir.join(format!("proof_states_{key}.jsonl"));
        let file = File::open(&path).with_context(|| format!("open {}", path.display()))?;
        let reader = BufReader::new(file);
        let mut rows = Vec::new();
        let (mut read, mut malformed, mut without) = (0usize, 0usize, 0usize);
        for line in reader.lines() {
            let line = line.with_context(|| format!("read {}", path.display()))?;
            if line.trim().is_empty() {
                continue;
            }
            read += 1;
            let value: serde_json::Value = match serde_json::from_str(&line) {
                Ok(v) => v,
                Err(_) => {
                    malformed += 1;
                    continue;
                },
            };
            let field = |f: &str| value.get(f).and_then(serde_json::Value::as_str);
            match (field("theorem"), field("goal")) {
                (Some(t), Some(g)) if !t.trim().is_empty() && !g.trim().is_empty() => {
                    rows.push((t.to_string(), g.to_string()));
                },
                _ => without += 1,
            }
        }
        let mut corpus = Corpus::from_rows(key, rows);
        if corpus.entries.is_empty() {
            bail!("{}: no usable (theorem, goal) rows", path.display());
        }
        corpus.lines_read = read;
        corpus.lines_malformed = malformed;
        corpus.lines_without_statement = without;
        Ok(corpus)
    }

    fn key_of(&self, i: usize) -> &StructuralKey {
        &self.keys[self.entries[i].key]
    }

    /// Distinct names that carry more than one distinct statement.
    pub fn homonym_names(&self) -> usize {
        self.by_name.values().filter(|v| v.len() > 1).count()
    }

    /// How much of the corpus the canonicaliser keyed at each tier, and how
    /// often distinct statements share one structural key.
    pub fn coverage(&self) -> Coverage {
        let mut tiers = TierCounts::default();
        for e in &self.entries {
            let k = &self.keys[e.key];
            match k.tier {
                KeyTier::Structural => tiers.structural += 1,
                KeyTier::Skeleton => tiers.skeleton += 1,
                KeyTier::Text => tiers.text += 1,
            }
            if k.complete {
                tiers.complete += 1;
            }
        }
        let (mut collision_keys, mut collision_statements) = (0usize, 0usize);
        for group in self.by_shape.values() {
            let texts = self.distinct_statements(group);
            if texts > 1 {
                collision_keys += 1;
                collision_statements += texts;
            }
        }
        Coverage {
            schema: COVERAGE_SCHEMA,
            scheme: canonical::SCHEME,
            corpus: self.key.clone(),
            lines_read: self.lines_read,
            lines_malformed: self.lines_malformed,
            lines_without_statement: self.lines_without_statement,
            rows: self.entries.len(),
            names: self.by_name.len(),
            homonym_names: self.homonym_names(),
            tiers,
            collision_keys,
            collision_statements,
        }
    }

    fn distinct_statements(&self, group: &[usize]) -> usize {
        group
            .iter()
            .map(|&i| self.entries[i].statement.as_str())
            .collect::<BTreeSet<_>>()
            .len()
    }

    /// Sample structural keys that distinct statements share: half the
    /// sample from the largest groups (trivial shapes), half from groups of
    /// exactly two (where a false merge is easiest to read). Each group lists
    /// at most six members.
    pub fn collisions(&self, limit: usize) -> Vec<CollisionRecord> {
        let mut multi: Vec<(&String, &Vec<usize>, usize)> = self
            .by_shape
            .iter()
            .map(|(k, g)| (k, g, self.distinct_statements(g)))
            .filter(|(_, _, n)| *n > 1)
            .collect();
        let mut picked: Vec<(&String, &Vec<usize>, usize)> = Vec::new();
        let mut largest = multi.clone();
        largest.sort_by(|x, y| y.2.cmp(&x.2).then_with(|| x.0.cmp(y.0)));
        picked.extend(largest.into_iter().take(limit / 2));
        multi.retain(|(k, _, n)| *n == 2 && !picked.iter().any(|(pk, _, _)| pk == k));
        picked.extend(multi.into_iter().take(limit - picked.len().min(limit)));

        picked
            .into_iter()
            .map(|(key, group, n)| {
                let mut seen = BTreeSet::new();
                let members = group
                    .iter()
                    .filter(|&&i| seen.insert(self.entries[i].statement.clone()))
                    .take(6)
                    .map(|&i| Member {
                        name: self.entries[i].name.clone(),
                        statement: self.entries[i].statement.clone(),
                    })
                    .collect();
                CollisionRecord {
                    schema: COLLISION_SCHEMA,
                    scheme: canonical::SCHEME,
                    corpus: self.key.clone(),
                    key: key.clone(),
                    shape: self.key_of(group[0]).shape.clone(),
                    distinct_statements: n,
                    members,
                }
            })
            .collect()
    }
}

/// Entries keyed at each canonicalisation tier, and how many of them the
/// parser read completely ([`StructuralKey::complete`]).
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct TierCounts {
    pub structural: usize,
    pub skeleton: usize,
    pub text: usize,
    pub complete: usize,
}

/// Per-corpus parse coverage and key-collision counts.
#[derive(Debug, Clone, Serialize)]
pub struct Coverage {
    pub schema: &'static str,
    pub scheme: &'static str,
    pub corpus: String,
    pub lines_read: usize,
    pub lines_malformed: usize,
    pub lines_without_statement: usize,
    /// Distinct `(name, statement)` rows.
    pub rows: usize,
    pub names: usize,
    /// Names with more than one distinct statement.
    pub homonym_names: usize,
    pub tiers: TierCounts,
    /// Structural keys shared by two or more distinct statement texts:
    /// alpha-variants of one statement, or distinct statements the scheme
    /// cannot tell apart.
    pub collision_keys: usize,
    /// Distinct statements inside those keys.
    pub collision_statements: usize,
}

/// One name and statement inside a sampled collision group.
#[derive(Debug, Clone, Serialize)]
pub struct Member {
    pub name: String,
    pub statement: String,
}

/// A structural key that distinct statements share, for review.
#[derive(Debug, Clone, Serialize)]
pub struct CollisionRecord {
    pub schema: &'static str,
    pub scheme: &'static str,
    pub corpus: String,
    pub key: String,
    pub shape: String,
    pub distinct_statements: usize,
    pub members: Vec<Member>,
}

/// How a candidate pair was found.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Join {
    /// The same theorem name in both corpora.
    NameExact,
    /// Names equal after [`fold_name`] but not before.
    NameFolded,
    /// Different names, identical statement text. Needs no canonicaliser,
    /// so it also finds synonyms among statements `dk-shape-v1` cannot read.
    Text,
    /// Different names, the same structural key.
    Shape,
    /// Different names, the same skeleton key and a different structural key.
    Skeleton,
}

/// The strongest tier at which a pair's statements agree.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Candidate {
    /// Identical text after whitespace collapsing.
    CognateExact,
    /// Different text, the same structural key: equal up to variable names
    /// and the spellings `dk-shape-v1` normalises.
    CognateShape,
    /// Only the skeleton keys agree: the statements differ in binders or
    /// sorts. For a name join this is a specialisation candidate.
    CognateSkeleton,
    /// Both statements parsed completely and no key agrees: a false friend
    /// or a specialisation the scheme cannot see. Only a probe or a kernel
    /// can tell which.
    Differs,
    /// The texts differ and at least one side did not parse completely, so
    /// the keys say nothing either way.
    Unparsed,
}

/// One side of a candidate pair.
#[derive(Debug, Clone, Serialize)]
pub struct Side {
    pub corpus: String,
    pub name: String,
    pub statement: String,
    /// `structural`, `skeleton` or `text`: how far the canonicaliser got.
    pub tier: &'static str,
    /// Whether the canonicaliser read the whole statement; when `false` the
    /// shape is a prefix and takes no part in shape classification.
    pub complete: bool,
    /// The canonical shape at that tier (normalised text for `text`).
    pub shape: String,
}

/// One review candidate. Never evidence: `evidence` is always `none`.
#[derive(Debug, Clone, Serialize)]
pub struct CandidateRecord {
    pub schema: &'static str,
    /// UUIDv8 content id of the statement pair (see the module docs).
    pub id: String,
    pub scheme: &'static str,
    pub join: Join,
    pub candidate: Candidate,
    pub a: Side,
    pub b: Side,
    /// Jaccard similarity, in thousandths, of the two shapes' constant and
    /// operator atoms (variables `v0`, `v1`, … and `PI` excluded). A ranking
    /// aid for review, not a measure of sameness.
    pub similarity_permille: u32,
    /// The shared name is generic (only with `--keep-generic`).
    pub generic_name: bool,
    pub evidence: LexiconEvidence,
}

/// Counts of candidates by classification.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct CandidateCounts {
    pub cognate_exact: usize,
    pub cognate_shape: usize,
    pub cognate_skeleton: usize,
    pub differs: usize,
    pub unparsed: usize,
}

impl CandidateCounts {
    fn add(&mut self, c: Candidate) {
        match c {
            Candidate::CognateExact => self.cognate_exact += 1,
            Candidate::CognateShape => self.cognate_shape += 1,
            Candidate::CognateSkeleton => self.cognate_skeleton += 1,
            Candidate::Differs => self.differs += 1,
            Candidate::Unparsed => self.unparsed += 1,
        }
    }

    pub fn total(&self) -> usize {
        self.cognate_exact
            + self.cognate_shape
            + self.cognate_skeleton
            + self.differs
            + self.unparsed
    }
}

/// Candidate counts for each join.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct JoinCounts {
    pub name_exact: CandidateCounts,
    pub name_folded: CandidateCounts,
    pub text: CandidateCounts,
    pub shape: CandidateCounts,
    pub skeleton: CandidateCounts,
}

impl JoinCounts {
    fn add(&mut self, join: Join, c: Candidate) {
        match join {
            Join::NameExact => self.name_exact.add(c),
            Join::NameFolded => self.name_folded.add(c),
            Join::Text => self.text.add(c),
            Join::Shape => self.shape.add(c),
            Join::Skeleton => self.skeleton.add(c),
        }
    }
}

/// What one pair scan found and what it skipped.
#[derive(Debug, Clone, Serialize)]
pub struct PairSummary {
    pub schema: &'static str,
    pub scheme: &'static str,
    pub pair: [String; 2],
    /// Folded names present in both corpora.
    pub folded_names_shared: usize,
    /// Of those, the generic ones not emitted (see [`is_generic`]).
    pub generic_names_skipped: usize,
    /// Raw-name pairs whose statement cross product exceeded the cap.
    pub name_pairs_capped: usize,
    /// Statement pairs inside those capped name pairs.
    pub statement_pairs_capped: usize,
    /// Identical-text groups over the size cap on either side, or too short
    /// (fewer than three tokens) to join two names on.
    pub text_groups_capped: usize,
    pub text_groups_uninformative: usize,
    /// Shape or skeleton groups over the size cap on either side.
    pub shape_groups_capped: usize,
    pub skeleton_groups_capped: usize,
    /// Shape or skeleton groups shared by both corpora but skipped as too
    /// little structure for a synonym (see [`informative`]).
    pub shape_groups_uninformative: usize,
    pub skeleton_groups_uninformative: usize,
    pub candidates: JoinCounts,
}

/// Limits that keep a scan's output reviewable.
#[derive(Debug, Clone)]
pub struct ScanOptions {
    /// Emit pairs whose shared name is generic.
    pub keep_generic: bool,
    /// Skip a shared name whose statement cross product exceeds this.
    pub max_pairs_per_name: usize,
    /// Skip a shape or skeleton group larger than this on either side.
    pub max_shape_group: usize,
}

impl Default for ScanOptions {
    fn default() -> Self {
        ScanOptions {
            keep_generic: false,
            max_pairs_per_name: 64,
            max_shape_group: 8,
        }
    }
}

fn atoms(shape: &str) -> BTreeSet<&str> {
    shape
        .split(|c: char| c.is_whitespace() || matches!(c, '(' | ')' | '[' | ']'))
        .filter(|t| !t.is_empty() && *t != "PI")
        .filter(|t| {
            !(t.len() > 1 && t.starts_with('v') && t[1..].chars().all(|c| c.is_ascii_digit()))
        })
        .collect()
}

/// Canonical sort atoms (`dk-shape-v1`'s `sort_of`) plus `ARROW`: the type
/// language. A shape made only of these and variables is a bare signature.
const TYPE_ATOMS: [&str; 9] = [
    "ARROW", "NAT", "INT", "BOOL", "REAL", "TYPE", "STRING", "LIST", "VEC",
];

/// Whether a skeleton carries enough structure to propose a synonym between
/// two *differently named* statements: at least three non-variable atoms,
/// at least one of them outside the type language, and no variable applied
/// to arguments. `dk-shape-v1` renames any short lower-case name to a
/// variable, so `cos 0 = 1`, `exp 0 = 1` and `n 0 = 1` all become
/// `(EQ (v0 0) 1)`; a variable in function position is the mark of that.
/// A bare `(summable v0)` says only that something is summable, and a bare
/// signature such as `int -> int -> int` is shared by every function of
/// that type. Name joins are not filtered: there the shared name anchors.
pub fn informative(skeleton: &str) -> bool {
    let chars: Vec<char> = skeleton.chars().collect();
    let variable_head = chars.windows(3).enumerate().any(|(i, w)| {
        w[0] == '(' && w[1] == 'v' && w[2].is_ascii_digit() && {
            let rest = &chars[i + 2..];
            let digits = rest.iter().take_while(|c| c.is_ascii_digit()).count();
            matches!(rest.get(digits), Some(' '))
        }
    });
    let constants: Vec<&str> = skeleton
        .split(|c: char| c.is_whitespace() || matches!(c, '(' | ')' | '[' | ']'))
        // `?` is an erased sort and `_` a hole: placeholders, not atoms.
        .filter(|t| !t.is_empty() && !matches!(*t, "PI" | "?" | "_"))
        .filter(|t| {
            !(t.len() > 1 && t.starts_with('v') && t[1..].chars().all(|c| c.is_ascii_digit()))
        })
        .collect();
    let beyond_types = constants.iter().any(|t| !TYPE_ATOMS.contains(t));
    !variable_head && constants.len() >= 3 && beyond_types
}

fn similarity_permille(a: &str, b: &str) -> u32 {
    let (sa, sb) = (atoms(a), atoms(b));
    let union = sa.union(&sb).count();
    if union == 0 {
        return 0;
    }
    (sa.intersection(&sb).count() * 1000 / union) as u32
}

fn classify(a: &Entry, ka: &StructuralKey, b: &Entry, kb: &StructuralKey) -> Candidate {
    if a.statement == b.statement {
        return Candidate::CognateExact;
    }
    // `complete` is false at the text tier, so this also covers unparsed text.
    if !ka.complete || !kb.complete {
        return Candidate::Unparsed;
    }
    if ka.tier == KeyTier::Structural && kb.tier == KeyTier::Structural && ka.key == kb.key {
        return Candidate::CognateShape;
    }
    if !ka.skeleton.is_empty() && ka.skeleton_key == kb.skeleton_key {
        return Candidate::CognateSkeleton;
    }
    Candidate::Differs
}

#[derive(Serialize)]
struct IdSide<'s> {
    corpus: &'s str,
    name: &'s str,
    statement: &'s str,
}

#[derive(Serialize)]
struct IdPair<'s> {
    a: IdSide<'s>,
    b: IdSide<'s>,
}

/// The order-independent content id of a statement pair.
pub fn pair_id(
    (ca, na, sa): (&str, &str, &str),
    (cb, nb, sb): (&str, &str, &str),
) -> Result<String> {
    let x = IdSide {
        corpus: ca,
        name: na,
        statement: sa,
    };
    let y = IdSide {
        corpus: cb,
        name: nb,
        statement: sb,
    };
    let pair = if (ca, na, sa) <= (cb, nb, sb) {
        IdPair { a: x, b: y }
    } else {
        IdPair { a: y, b: x }
    };
    Ok(crate::ids::content_id(&pair)?.to_string())
}

fn side(c: &Corpus, i: usize) -> Side {
    let e = &c.entries[i];
    let k = c.key_of(i);
    Side {
        corpus: c.key.clone(),
        name: e.name.clone(),
        statement: e.statement.clone(),
        tier: k.tier.as_str(),
        complete: k.complete,
        shape: k.shape.clone(),
    }
}

fn record(
    a: &Corpus,
    ia: usize,
    b: &Corpus,
    ib: usize,
    join: Join,
    candidate: Candidate,
    generic_name: bool,
) -> Result<CandidateRecord> {
    let (ea, eb) = (&a.entries[ia], &b.entries[ib]);
    Ok(CandidateRecord {
        schema: CANDIDATE_SCHEMA,
        id: pair_id(
            (a.key.as_str(), ea.name.as_str(), ea.statement.as_str()),
            (b.key.as_str(), eb.name.as_str(), eb.statement.as_str()),
        )?,
        scheme: canonical::SCHEME,
        join,
        candidate,
        a: side(a, ia),
        b: side(b, ib),
        similarity_permille: similarity_permille(&a.key_of(ia).shape, &b.key_of(ib).shape),
        generic_name,
        evidence: LexiconEvidence::None,
    })
}

/// Scan one corpus pair, passing every candidate to `emit` in a fixed
/// order: name joins by folded name, then text, shape and skeleton joins,
/// each by key. A pair is reported by the first join that finds it.
///
/// # Errors
///
/// Whatever `emit` returns, or a failure to derive a content id.
pub fn scan_pair(
    a: &Corpus,
    b: &Corpus,
    opts: &ScanOptions,
    emit: &mut dyn FnMut(&CandidateRecord) -> Result<()>,
) -> Result<PairSummary> {
    let mut summary = PairSummary {
        schema: PAIR_SUMMARY_SCHEMA,
        scheme: canonical::SCHEME,
        pair: [a.key.clone(), b.key.clone()],
        folded_names_shared: 0,
        generic_names_skipped: 0,
        name_pairs_capped: 0,
        statement_pairs_capped: 0,
        text_groups_capped: 0,
        text_groups_uninformative: 0,
        shape_groups_capped: 0,
        skeleton_groups_capped: 0,
        shape_groups_uninformative: 0,
        skeleton_groups_uninformative: 0,
        candidates: JoinCounts::default(),
    };

    // 1. Name joins: same folded name.
    for (folded, names_a) in &a.by_fold {
        let Some(names_b) = b.by_fold.get(folded) else {
            continue;
        };
        summary.folded_names_shared += 1;
        let generic = is_generic(folded);
        if generic && !opts.keep_generic {
            summary.generic_names_skipped += 1;
            continue;
        }
        for na in names_a {
            for nb in names_b {
                let (ga, gb) = (&a.by_name[na], &b.by_name[nb]);
                let product = ga.len() * gb.len();
                if product > opts.max_pairs_per_name {
                    summary.name_pairs_capped += 1;
                    summary.statement_pairs_capped += product;
                    continue;
                }
                let join = if na == nb {
                    Join::NameExact
                } else {
                    Join::NameFolded
                };
                for &ia in ga {
                    for &ib in gb {
                        let c =
                            classify(&a.entries[ia], a.key_of(ia), &b.entries[ib], b.key_of(ib));
                        summary.candidates.add(join, c);
                        emit(&record(a, ia, b, ib, join, c, generic)?)?;
                    }
                }
            }
        }
    }

    let same_name =
        |ia: usize, ib: usize| fold_name(&a.entries[ia].name) == fold_name(&b.entries[ib].name);
    let same_text = |ia: usize, ib: usize| a.entries[ia].statement == b.entries[ib].statement;

    // 2. Text joins: different names, identical statement text. A statement
    //    of fewer than three tokens (`T`, `x = y`) says too little to join on.
    for (text, ga) in &a.by_statement {
        let Some(gb) = b.by_statement.get(text) else {
            continue;
        };
        if ga.len() > opts.max_shape_group || gb.len() > opts.max_shape_group {
            summary.text_groups_capped += 1;
            continue;
        }
        if canonical::token_count(text) < 3 {
            summary.text_groups_uninformative += 1;
            continue;
        }
        for &ia in ga {
            for &ib in gb {
                if same_name(ia, ib) {
                    continue;
                }
                summary.candidates.add(Join::Text, Candidate::CognateExact);
                emit(&record(
                    a,
                    ia,
                    b,
                    ib,
                    Join::Text,
                    Candidate::CognateExact,
                    false,
                )?)?;
            }
        }
    }

    // 3. Shape joins: different names, the same structural key, and not
    //    already joined by text.
    for (key, ga) in &a.by_shape {
        let Some(gb) = b.by_shape.get(key) else {
            continue;
        };
        if ga.len() > opts.max_shape_group || gb.len() > opts.max_shape_group {
            summary.shape_groups_capped += 1;
            continue;
        }
        if !informative(&a.key_of(ga[0]).skeleton) {
            summary.shape_groups_uninformative += 1;
            continue;
        }
        for &ia in ga {
            for &ib in gb {
                if same_name(ia, ib) || same_text(ia, ib) {
                    continue;
                }
                let c = classify(&a.entries[ia], a.key_of(ia), &b.entries[ib], b.key_of(ib));
                summary.candidates.add(Join::Shape, c);
                emit(&record(a, ia, b, ib, Join::Shape, c, false)?)?;
            }
        }
    }

    // 4. Skeleton joins: different names, the same skeleton key, and not
    //    already joined by text or shape.
    for (key, ga) in &a.by_skeleton {
        let Some(gb) = b.by_skeleton.get(key) else {
            continue;
        };
        if ga.len() > opts.max_shape_group || gb.len() > opts.max_shape_group {
            summary.skeleton_groups_capped += 1;
            continue;
        }
        if !informative(&a.key_of(ga[0]).skeleton) {
            summary.skeleton_groups_uninformative += 1;
            continue;
        }
        for &ia in ga {
            for &ib in gb {
                let (ka, kb) = (a.key_of(ia), b.key_of(ib));
                let shape_match = ka.tier == KeyTier::Structural
                    && kb.tier == KeyTier::Structural
                    && ka.key == kb.key;
                if same_name(ia, ib) || same_text(ia, ib) || shape_match {
                    continue;
                }
                let c = classify(&a.entries[ia], ka, &b.entries[ib], kb);
                summary.candidates.add(Join::Skeleton, c);
                emit(&record(a, ia, b, ib, Join::Skeleton, c, false)?)?;
            }
        }
    }

    Ok(summary)
}

/// Serialise `value` as one JCS line (RFC 8785 plus a final LF).
pub fn jcs_line<T: Serialize>(value: &T) -> Result<Vec<u8>> {
    let mut bytes = serde_json_canonicalizer::to_vec(value)?;
    bytes.push(b'\n');
    Ok(bytes)
}

/// A whole scan: which pairs, where the corpora are, where output goes.
#[derive(Debug, Clone)]
pub struct RunOptions {
    pub training_dir: PathBuf,
    pub pairs: Vec<(String, String)>,
    pub out: PathBuf,
    pub scan: ScanOptions,
    /// Collision groups to sample per corpus.
    pub collision_samples: usize,
}

/// What a run produced, for the CLI to print. Timings are reported here and
/// never written into the JCS files, which stay deterministic.
#[derive(Debug, Clone)]
pub struct RunReport {
    pub coverage: Vec<Coverage>,
    pub pairs: Vec<PairSummary>,
    pub load_times: Vec<(String, Duration)>,
    pub pair_times: Vec<(String, Duration)>,
    pub total: Duration,
}

fn write_lines<T: Serialize>(path: &Path, items: &[T]) -> Result<()> {
    let mut w =
        BufWriter::new(File::create(path).with_context(|| format!("create {}", path.display()))?);
    for item in items {
        w.write_all(&jcs_line(item)?)?;
    }
    w.flush()?;
    Ok(())
}

/// Load every corpus the pairs name (each once), scan each pair, and write
/// `pairs/<a>__<b>.jsonl`, `summary.jsonl`, `coverage.jsonl` and
/// `collisions/<corpus>.jsonl` under `opts.out`.
///
/// # Errors
///
/// A corpus fails to load, or an output file cannot be written.
pub fn run(opts: &RunOptions) -> Result<RunReport> {
    let started = Instant::now();
    if opts.pairs.is_empty() {
        bail!("no corpus pairs to scan: pass --pair A:B or --preset");
    }
    let needed: BTreeSet<&str> = opts
        .pairs
        .iter()
        .flat_map(|(a, b)| [a.as_str(), b.as_str()])
        .collect();

    let mut corpora: BTreeMap<String, Corpus> = BTreeMap::new();
    let mut load_times = Vec::new();
    for key in needed {
        let t = Instant::now();
        let corpus = Corpus::load(&opts.training_dir, key)?;
        load_times.push((key.to_string(), t.elapsed()));
        corpora.insert(key.to_string(), corpus);
    }

    let pairs_dir = opts.out.join("pairs");
    let collisions_dir = opts.out.join("collisions");
    fs::create_dir_all(&pairs_dir).with_context(|| format!("create {}", pairs_dir.display()))?;
    fs::create_dir_all(&collisions_dir)
        .with_context(|| format!("create {}", collisions_dir.display()))?;
    // A re-run over a different pair set must not leave the previous run's
    // files beside this run's summary. Only the scan's own `.jsonl` files
    // are removed; anything else in the directory is left alone.
    for dir in [&pairs_dir, &collisions_dir] {
        for entry in fs::read_dir(dir).with_context(|| format!("read {}", dir.display()))? {
            let path = entry?.path();
            if path.extension().and_then(|e| e.to_str()) == Some("jsonl") {
                fs::remove_file(&path).with_context(|| format!("remove {}", path.display()))?;
            }
        }
    }

    let coverage: Vec<Coverage> = corpora.values().map(Corpus::coverage).collect();
    write_lines(&opts.out.join("coverage.jsonl"), &coverage)?;
    for c in corpora.values() {
        write_lines(
            &collisions_dir.join(format!("{}.jsonl", c.key)),
            &c.collisions(opts.collision_samples),
        )?;
    }

    let mut summaries = Vec::new();
    let mut pair_times = Vec::new();
    for (ka, kb) in &opts.pairs {
        let t = Instant::now();
        let path = pairs_dir.join(format!("{ka}__{kb}.jsonl"));
        let mut w = BufWriter::new(
            File::create(&path).with_context(|| format!("create {}", path.display()))?,
        );
        let summary = scan_pair(&corpora[ka], &corpora[kb], &opts.scan, &mut |rec| {
            w.write_all(&jcs_line(rec)?)?;
            Ok(())
        })?;
        w.flush()?;
        pair_times.push((format!("{ka}:{kb}"), t.elapsed()));
        summaries.push(summary);
    }
    write_lines(&opts.out.join("summary.jsonl"), &summaries)?;

    Ok(RunReport {
        coverage,
        pairs: summaries,
        load_times,
        pair_times,
        total: started.elapsed(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn folding_unifies_case_namespace_and_separator() {
        assert_eq!(fold_name("nat.add_comm"), "add_comm");
        assert_eq!(fold_name("ADD_COMM"), "add_comm");
        assert_eq!(fold_name("add-comm"), "add_comm");
        assert_eq!(fold_name("Foo::bar"), "bar");
        assert_eq!(fold_name("_x_"), "x");
    }

    #[test]
    fn generic_names_are_recognised() {
        for g in [
            "lemma",
            "lemma_3",
            "lemma3",
            "aux2",
            "th27",
            "ex1",
            "z",
            "anonymous",
            "step2'",
        ] {
            assert!(is_generic(&fold_name(g)), "{g} should be generic");
        }
        for n in ["add_comm", "append_assoc", "cos_add", "zip_unzip", "ext"] {
            assert!(!is_generic(&fold_name(n)), "{n} should not be generic");
        }
    }

    #[test]
    fn presets_expand_as_documented() {
        assert_eq!(preset_pairs("learning").unwrap().len(), 2);
        assert_eq!(preset_pairs("spanning").unwrap().len(), 28);
        assert_eq!(preset_pairs("in-family").unwrap().len(), 5);
        assert_eq!(preset_pairs("full").unwrap().len(), 33);
        assert!(preset_pairs("everything").is_none());
    }

    #[test]
    fn pair_arguments_are_validated() {
        assert_eq!(
            parse_pair("hol4:hol_light").unwrap(),
            ("hol4".to_string(), "hol_light".to_string())
        );
        assert!(parse_pair("hol4").is_err());
        assert!(parse_pair("hol4:hol4").is_err());
        assert!(parse_pair("../etc:hol4").is_err());
        // `a__b:c` and `a:b__c` would both write pairs/a__b__c.jsonl
        assert!(parse_pair("a__b:c").is_err());
    }

    #[test]
    fn similarity_ignores_variables_and_binders() {
        assert_eq!(
            similarity_permille("(EQ (ADD v0 v1) (ADD v1 v0))", "(EQ (ADD v2 v3) v4)"),
            1000
        );
        assert_eq!(
            similarity_permille("(EQ (ADD v0 v1))", "(LE (MUL v0 v1))"),
            0
        );
        assert_eq!(similarity_permille("", ""), 0);
    }

    #[test]
    fn informative_rejects_variable_heads_and_bare_predicates() {
        // `cos 0 = 1` and `n 0 = 1` under dk-shape-v1
        assert!(!informative("(EQ (v0 0) 1)"));
        assert!(!informative("(EQ (v0 v1 v2) (v3 v1 v2))"));
        assert!(!informative("(summable v0)"));
        assert!(informative("(EQ (ADD v0 0) v0)"));
        assert!(informative("(LT v0 (2 ^ v0))"));
        assert!(informative(
            "(EQ (MUL (MUL v0 v1) v2) (MUL v0 (MUL v1 v2)))"
        ));
        // `v10` in function position is still a variable head
        assert!(!informative("(EQ (v10 0) (ADD 1 1))"));
        // bare signatures: λProlog `int -> int -> int`, Dedukti `Int -> Int -> Int`
        assert!(!informative("(ARROW INT (ARROW INT INT))"));
        assert!(!informative("(ARROW (ARROW v0 v0) (ARROW v0 v0))"));
        // ...and their skeletons, where sorts render as `?`
        assert!(!informative("(ARROW ? (ARROW ? ?))"));
        assert!(!informative("(ARROW ? ?)"));
        assert!(informative("(ARROW (LE v0 v1) (LE (ADD v0 1) (ADD v1 1)))"));
    }

    #[test]
    fn text_join_counts_lexical_tokens_not_words() {
        // one whitespace field, eight tokens: enough to join two names on
        assert!(canonical::token_count("f(x)=g(x)") >= 3);
        assert!(canonical::token_count("T") < 3);
        assert!(canonical::token_count("x = y") >= 3);
    }

    #[test]
    fn pair_ids_ignore_side_order() {
        let x = ("hol4", "ADD_COMM", "!m n. m + n = n + m");
        let y = ("hol_light", "ADD_SYM", "!m n. m + n = n + m");
        assert_eq!(pair_id(x, y).unwrap(), pair_id(y, x).unwrap());
        assert_ne!(pair_id(x, y).unwrap(), pair_id(x, x).unwrap());
    }
}
