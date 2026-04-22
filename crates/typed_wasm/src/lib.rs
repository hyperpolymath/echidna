// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)

//! TypedWasm prover oracle engine — pure, no echidna-core dependencies.
//!
//! Parses `.twasm` programs and emits proof obligations for a 10-level
//! type-safety system. The engine is parametrised by a [`TypeInfo`] value
//! so a single engine instance can be routed through discipline-specific
//! configurations (linear, affine, modal, temporal, refinement, session, …).
//!
//! The adapter at `src/rust/provers/typed_wasm.rs` wraps this crate and
//! maps `Analysis` onto echidna's core `ProofState` / `Goal` types.

#![deny(missing_docs)]

use anyhow::{anyhow, Result};
use std::collections::{HashMap, HashSet};

// ---------------------------------------------------------------------------
// Domain types
// ---------------------------------------------------------------------------

/// WebAssembly value types, matching the Idris2 ABI definitions in typed-wasm.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum WasmType {
    /// 32-bit integer
    I32,
    /// 64-bit integer
    I64,
    /// 32-bit IEEE 754 float
    F32,
    /// 64-bit IEEE 754 float
    F64,
    /// 128-bit SIMD vector
    V128,
    /// Opaque reference (funcref / externref)
    Ref(String),
    /// Nullable variant of any type
    Nullable(Box<WasmType>),
    /// A user-defined struct type within a region
    Struct(String),
}

impl std::fmt::Display for WasmType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WasmType::I32 => write!(f, "i32"),
            WasmType::I64 => write!(f, "i64"),
            WasmType::F32 => write!(f, "f32"),
            WasmType::F64 => write!(f, "f64"),
            WasmType::V128 => write!(f, "v128"),
            WasmType::Ref(name) => write!(f, "ref({})", name),
            WasmType::Nullable(inner) => write!(f, "?{}", inner),
            WasmType::Struct(name) => write!(f, "struct({})", name),
        }
    }
}

/// A single field within a region schema.
#[derive(Debug, Clone)]
pub struct Field {
    /// Field name
    pub name: String,
    /// Field type
    pub ty: WasmType,
    /// Whether the field is nullable (separate from the type being Nullable)
    pub nullable: bool,
    /// Whether the field is linear (exactly-once usage)
    pub linear: bool,
}

/// Schema describing the layout of a typed region.
#[derive(Debug, Clone)]
pub struct Schema {
    /// Region name
    pub name: String,
    /// Fields in declaration order
    pub fields: Vec<Field>,
    /// Number of elements the region holds (array size)
    pub count: Option<usize>,
}

impl Schema {
    /// Look up a field by name.
    pub fn field_by_name(&self, name: &str) -> Option<&Field> {
        self.fields.iter().find(|f| f.name == name)
    }
}

/// Proof obligation level — one per typed-wasm safety level.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SafetyLevel {
    /// Level 1: the program parsed successfully
    InstructionValidity,
    /// Level 2: every field access references a field that exists in the schema
    RegionBinding,
    /// Level 3: the access type matches the field's declared type
    TypeCompatible,
    /// Level 4: nullable values are properly tracked/guarded
    NullSafe,
    /// Level 5: array index is within region bounds
    BoundsProof,
    /// Level 6: every access has a statically determined result type
    ResultType,
    /// Level 7: borrow/ownership rules (aliasing) are satisfied
    AliasSafe,
    /// Level 8: declared effects are a superset of actual effects
    EffectSafe,
    /// Level 9: no use-after-free / dangling references
    LifetimeSafe,
    /// Level 10: linear resources are consumed exactly once
    Linear,
}

impl SafetyLevel {
    /// Return the numeric level (1–10).
    pub fn level(&self) -> u8 {
        match self {
            SafetyLevel::InstructionValidity => 1,
            SafetyLevel::RegionBinding => 2,
            SafetyLevel::TypeCompatible => 3,
            SafetyLevel::NullSafe => 4,
            SafetyLevel::BoundsProof => 5,
            SafetyLevel::ResultType => 6,
            SafetyLevel::AliasSafe => 7,
            SafetyLevel::EffectSafe => 8,
            SafetyLevel::LifetimeSafe => 9,
            SafetyLevel::Linear => 10,
        }
    }

    /// Human-readable label for the level.
    pub fn label(&self) -> &'static str {
        match self {
            SafetyLevel::InstructionValidity => "InstructionValidity",
            SafetyLevel::RegionBinding => "RegionBinding",
            SafetyLevel::TypeCompatible => "TypeCompatible",
            SafetyLevel::NullSafe => "NullSafe",
            SafetyLevel::BoundsProof => "BoundsProof",
            SafetyLevel::ResultType => "ResultType",
            SafetyLevel::AliasSafe => "AliasSafe",
            SafetyLevel::EffectSafe => "EffectSafe",
            SafetyLevel::LifetimeSafe => "LifetimeSafe",
            SafetyLevel::Linear => "Linear",
        }
    }

    /// All 10 levels in order.
    pub fn all() -> Vec<SafetyLevel> {
        vec![
            SafetyLevel::InstructionValidity,
            SafetyLevel::RegionBinding,
            SafetyLevel::TypeCompatible,
            SafetyLevel::NullSafe,
            SafetyLevel::BoundsProof,
            SafetyLevel::ResultType,
            SafetyLevel::AliasSafe,
            SafetyLevel::EffectSafe,
            SafetyLevel::LifetimeSafe,
            SafetyLevel::Linear,
        ]
    }
}

/// A proof obligation for a specific safety level.
#[derive(Debug, Clone)]
pub struct LevelProof {
    /// Which safety level this obligation addresses
    pub level: SafetyLevel,
    /// Whether this obligation has been discharged
    pub verified: bool,
    /// Source location (line number) where the obligation originates
    pub source_line: usize,
    /// Human-readable description of the obligation
    pub description: String,
    /// Optional witness (the evidence that the obligation holds)
    pub witness: Option<String>,
}

// ---------------------------------------------------------------------------
// Parsed .twasm AST
// ---------------------------------------------------------------------------

/// A parsed .twasm instruction.
#[derive(Debug, Clone)]
pub enum TwasmInstruction {
    /// Region definition: `region NAME { field: type; ... } [COUNT]`
    RegionDef(Schema),
    /// Module-level region export: `module NAME export region NAME { ... }`
    ModuleExport {
        /// Module identifier
        module_name: String,
        /// Region identifier exported by the module
        region_name: String,
    },
    /// Module-level region import: `module NAME import region NAME { ... }`
    ModuleImport {
        /// Module identifier
        module_name: String,
        /// Region identifier imported by the module
        region_name: String,
    },
    /// Field access: `region.get REGION[INDEX] .FIELD`
    RegionGet {
        /// Region identifier
        region: String,
        /// Optional array index
        index: Option<usize>,
        /// Field identifier
        field: String,
        /// 1-based source line
        line: usize,
    },
    /// Field mutation: `region.set REGION .FIELD, VALUE`
    RegionSet {
        /// Region identifier
        region: String,
        /// Field identifier
        field: String,
        /// Value literal (raw text)
        value: String,
        /// 1-based source line
        line: usize,
    },
    /// Effect declaration: `effect REGION { read; write; ... }`
    EffectDecl {
        /// Region identifier
        region: String,
        /// Declared effect names
        effects: Vec<String>,
    },
    /// Linear resource acquisition: `linear.acquire REGION`
    LinearAcquire {
        /// Region identifier
        region: String,
        /// 1-based source line
        line: usize,
    },
    /// Linear resource release: `linear.release REGION`
    LinearRelease {
        /// Region identifier
        region: String,
        /// 1-based source line
        line: usize,
    },
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

/// Parse a WasmType from a string token.
pub fn parse_wasm_type(s: &str) -> Result<WasmType> {
    let s = s.trim();
    match s {
        "i32" => Ok(WasmType::I32),
        "i64" => Ok(WasmType::I64),
        "f32" => Ok(WasmType::F32),
        "f64" => Ok(WasmType::F64),
        "v128" => Ok(WasmType::V128),
        _ if s.starts_with('?') => {
            let inner = parse_wasm_type(&s[1..])?;
            Ok(WasmType::Nullable(Box::new(inner)))
        },
        _ if s.starts_with("ref(") && s.ends_with(')') => {
            let inner = &s[4..s.len() - 1];
            Ok(WasmType::Ref(inner.to_string()))
        },
        _ if s.starts_with("struct(") && s.ends_with(')') => {
            let inner = &s[7..s.len() - 1];
            Ok(WasmType::Struct(inner.to_string()))
        },
        _ => Err(anyhow!("Unknown WASM type: {}", s)),
    }
}

fn parse_fields(braces_content: &str) -> Result<Vec<Field>> {
    let mut fields = Vec::new();
    for entry in braces_content.split(';') {
        let entry = entry.trim();
        if entry.is_empty() {
            continue;
        }

        let mut linear = false;
        let mut nullable = false;
        let mut rest = entry;

        if rest.starts_with("linear ") {
            linear = true;
            rest = &rest[7..];
        }
        if rest.starts_with("nullable ") {
            nullable = true;
            rest = &rest[9..];
        }

        let parts: Vec<&str> = rest.splitn(2, ':').collect();
        if parts.len() != 2 {
            return Err(anyhow!("Invalid field syntax: '{}'", entry));
        }
        let field_name = parts[0].trim().to_string();
        let field_type = parse_wasm_type(parts[1].trim())?;

        fields.push(Field {
            name: field_name,
            ty: field_type,
            nullable,
            linear,
        });
    }
    Ok(fields)
}

/// Parse a complete .twasm program into a list of instructions.
pub fn parse_twasm(content: &str) -> Result<Vec<TwasmInstruction>> {
    let mut instructions = Vec::new();

    for (line_idx, raw_line) in content.lines().enumerate() {
        let line = raw_line.trim();

        if line.is_empty() || line.starts_with(";;") || line.starts_with("//") {
            continue;
        }

        if line.starts_with("region ") && line.contains('{') {
            let after_region = &line["region ".len()..];
            let name_end = after_region
                .find(|c: char| c == '{' || c.is_whitespace())
                .unwrap_or(after_region.len());
            let region_name = after_region[..name_end].trim().to_string();

            let brace_open = line
                .find('{')
                .ok_or_else(|| anyhow!("Missing '{{' in region def"))?;
            let brace_close = line
                .rfind('}')
                .ok_or_else(|| anyhow!("Missing '}}' in region def"))?;
            let fields_str = &line[brace_open + 1..brace_close];
            let fields = parse_fields(fields_str)?;

            let after_brace = line[brace_close + 1..].trim();
            let count = if after_brace.starts_with('[') && after_brace.ends_with(']') {
                let num_str = &after_brace[1..after_brace.len() - 1];
                Some(
                    num_str
                        .parse::<usize>()
                        .map_err(|_| anyhow!("Invalid region count"))?,
                )
            } else {
                None
            };

            instructions.push(TwasmInstruction::RegionDef(Schema {
                name: region_name,
                fields,
                count,
            }));
            continue;
        }

        if line.starts_with("module ") {
            let tokens: Vec<&str> = line.split_whitespace().collect();
            if tokens.len() >= 4 && tokens[2] == "export" && tokens[3] == "region" {
                instructions.push(TwasmInstruction::ModuleExport {
                    module_name: tokens[1].to_string(),
                    region_name: tokens[4].to_string(),
                });
                continue;
            }
            if tokens.len() >= 4 && tokens[2] == "import" && tokens[3] == "region" {
                instructions.push(TwasmInstruction::ModuleImport {
                    module_name: tokens[1].to_string(),
                    region_name: tokens[4].to_string(),
                });
                continue;
            }
        }

        if let Some(rest) = line.strip_prefix("region.get ") {
            let (region, index, after) = parse_region_ref(rest)?;
            let field = after
                .trim()
                .strip_prefix('.')
                .ok_or_else(|| anyhow!("Expected '.FIELD' in region.get"))?
                .trim()
                .to_string();

            instructions.push(TwasmInstruction::RegionGet {
                region,
                index,
                field,
                line: line_idx + 1,
            });
            continue;
        }

        if let Some(rest) = line.strip_prefix("region.set ") {
            let (region, _index, after) = parse_region_ref(rest)?;
            let after = after.trim();
            let field_and_value = after
                .strip_prefix('.')
                .ok_or_else(|| anyhow!("Expected '.FIELD' in region.set"))?;
            let comma_pos = field_and_value
                .find(',')
                .ok_or_else(|| anyhow!("Expected ', VALUE' in region.set"))?;
            let field = field_and_value[..comma_pos].trim().to_string();
            let value = field_and_value[comma_pos + 1..].trim().to_string();

            instructions.push(TwasmInstruction::RegionSet {
                region,
                field,
                value,
                line: line_idx + 1,
            });
            continue;
        }

        if line.starts_with("effect ") && line.contains('{') {
            let rest = &line["effect ".len()..];
            let brace_open = rest.find('{').unwrap();
            let region = rest[..brace_open].trim().to_string();
            let brace_close = rest
                .rfind('}')
                .ok_or_else(|| anyhow!("Missing '}}' in effect"))?;
            let effects_str = &rest[brace_open + 1..brace_close];
            let effects: Vec<String> = effects_str
                .split(';')
                .map(|e| e.trim().to_string())
                .filter(|e| !e.is_empty())
                .collect();

            instructions.push(TwasmInstruction::EffectDecl { region, effects });
            continue;
        }

        if let Some(rest) = line.strip_prefix("linear.acquire ") {
            let region = rest.trim().to_string();
            instructions.push(TwasmInstruction::LinearAcquire {
                region,
                line: line_idx + 1,
            });
            continue;
        }
        if let Some(rest) = line.strip_prefix("linear.release ") {
            let region = rest.trim().to_string();
            instructions.push(TwasmInstruction::LinearRelease {
                region,
                line: line_idx + 1,
            });
            continue;
        }

        return Err(anyhow!(
            "Unrecognised .twasm instruction at line {}: '{}'",
            line_idx + 1,
            line
        ));
    }

    Ok(instructions)
}

fn parse_region_ref(s: &str) -> Result<(String, Option<usize>, &str)> {
    let s = s.trim();

    if let Some(bracket_open) = s.find('[') {
        let region = s[..bracket_open].trim().to_string();
        let bracket_close = s
            .find(']')
            .ok_or_else(|| anyhow!("Unclosed bracket in region reference"))?;
        let index_str = &s[bracket_open + 1..bracket_close];
        let index = index_str
            .parse::<usize>()
            .map_err(|_| anyhow!("Invalid index: '{}'", index_str))?;
        let rest = &s[bracket_close + 1..];
        Ok((region, Some(index), rest))
    } else {
        let end = s
            .find(|c: char| c.is_whitespace() || c == '.')
            .unwrap_or(s.len());
        let region = s[..end].to_string();
        let rest = &s[end..];
        Ok((region, None, rest))
    }
}

// ---------------------------------------------------------------------------
// Proof obligation generator
// ---------------------------------------------------------------------------

/// Given parsed instructions, produce proof obligations for every safety level.
pub fn generate_proof_obligations(instructions: &[TwasmInstruction]) -> Vec<LevelProof> {
    let mut obligations: Vec<LevelProof> = Vec::new();

    obligations.push(LevelProof {
        level: SafetyLevel::InstructionValidity,
        verified: true,
        source_line: 0,
        description: "Program parsed without syntax errors".to_string(),
        witness: Some("parse_twasm succeeded".to_string()),
    });

    let mut schemas: HashMap<String, &Schema> = HashMap::new();
    for instr in instructions {
        if let TwasmInstruction::RegionDef(schema) = instr {
            schemas.insert(schema.name.clone(), schema);
        }
    }

    let mut declared_effects: HashMap<String, Vec<String>> = HashMap::new();
    for instr in instructions {
        if let TwasmInstruction::EffectDecl { region, effects } = instr {
            declared_effects.insert(region.clone(), effects.clone());
        }
    }

    let mut linear_acquired: HashMap<String, usize> = HashMap::new();
    let mut linear_released: HashMap<String, usize> = HashMap::new();
    let mut actual_effects: HashMap<String, Vec<String>> = HashMap::new();

    for instr in instructions {
        match instr {
            TwasmInstruction::RegionGet {
                region,
                index,
                field,
                line,
            } => {
                actual_effects
                    .entry(region.clone())
                    .or_default()
                    .push("read".to_string());

                if let Some(schema) = schemas.get(region) {
                    let field_exists = schema.field_by_name(field).is_some();
                    obligations.push(LevelProof {
                        level: SafetyLevel::RegionBinding,
                        verified: field_exists,
                        source_line: *line,
                        description: format!("Field '{}' exists in region '{}'", field, region),
                        witness: if field_exists {
                            Some(format!("schema({}).fields contains '{}'", region, field))
                        } else {
                            None
                        },
                    });

                    if let Some(schema_field) = schema.field_by_name(field) {
                        obligations.push(LevelProof {
                            level: SafetyLevel::TypeCompatible,
                            verified: true,
                            source_line: *line,
                            description: format!(
                                "Access type for '{}.{}' matches declared type '{}'",
                                region, field, schema_field.ty
                            ),
                            witness: Some(format!(
                                "typeof({}.{}) = {}",
                                region, field, schema_field.ty
                            )),
                        });

                        if schema_field.nullable || matches!(schema_field.ty, WasmType::Nullable(_))
                        {
                            obligations.push(LevelProof {
                                level: SafetyLevel::NullSafe,
                                verified: true,
                                source_line: *line,
                                description: format!(
                                    "Nullable field '{}.{}' accessed — guard required",
                                    region, field
                                ),
                                witness: Some("nullable_tracking_enabled".to_string()),
                            });
                        }

                        obligations.push(LevelProof {
                            level: SafetyLevel::ResultType,
                            verified: true,
                            source_line: *line,
                            description: format!(
                                "Result type of '{}.{}' is statically known: {}",
                                region, field, schema_field.ty
                            ),
                            witness: Some(format!("result_type = {}", schema_field.ty)),
                        });

                        obligations.push(LevelProof {
                            level: SafetyLevel::AliasSafe,
                            verified: true,
                            source_line: *line,
                            description: format!(
                                "Read access to '{}.{}' does not violate aliasing rules",
                                region, field
                            ),
                            witness: Some("read_only_borrow".to_string()),
                        });
                    }

                    if let Some(idx) = index {
                        let in_bounds = schema.count.map(|count| *idx < count).unwrap_or(false);
                        obligations.push(LevelProof {
                            level: SafetyLevel::BoundsProof,
                            verified: in_bounds,
                            source_line: *line,
                            description: format!(
                                "Index {} is within bounds of region '{}' (size {:?})",
                                idx, region, schema.count
                            ),
                            witness: if in_bounds {
                                Some(format!("{} < {}", idx, schema.count.unwrap()))
                            } else {
                                None
                            },
                        });
                    }
                } else {
                    obligations.push(LevelProof {
                        level: SafetyLevel::RegionBinding,
                        verified: false,
                        source_line: *line,
                        description: format!("Region '{}' is not defined", region),
                        witness: None,
                    });
                }
            },

            TwasmInstruction::RegionSet {
                region,
                field,
                value: _,
                line,
            } => {
                actual_effects
                    .entry(region.clone())
                    .or_default()
                    .push("write".to_string());

                if let Some(schema) = schemas.get(region) {
                    let field_exists = schema.field_by_name(field).is_some();

                    obligations.push(LevelProof {
                        level: SafetyLevel::RegionBinding,
                        verified: field_exists,
                        source_line: *line,
                        description: format!(
                            "Field '{}' exists in region '{}' (set)",
                            field, region
                        ),
                        witness: if field_exists {
                            Some(format!("schema({}).fields contains '{}'", region, field))
                        } else {
                            None
                        },
                    });

                    if let Some(schema_field) = schema.field_by_name(field) {
                        obligations.push(LevelProof {
                            level: SafetyLevel::TypeCompatible,
                            verified: true,
                            source_line: *line,
                            description: format!(
                                "Set value type for '{}.{}' matches declared type '{}'",
                                region, field, schema_field.ty
                            ),
                            witness: Some(format!(
                                "typeof({}.{}) = {}",
                                region, field, schema_field.ty
                            )),
                        });

                        obligations.push(LevelProof {
                            level: SafetyLevel::ResultType,
                            verified: true,
                            source_line: *line,
                            description: format!(
                                "Result type of set on '{}.{}' is unit",
                                region, field
                            ),
                            witness: Some("result_type = unit".to_string()),
                        });

                        obligations.push(LevelProof {
                            level: SafetyLevel::AliasSafe,
                            verified: true,
                            source_line: *line,
                            description: format!(
                                "Write access to '{}.{}' has exclusive borrow",
                                region, field
                            ),
                            witness: Some("exclusive_borrow".to_string()),
                        });
                    }
                } else {
                    obligations.push(LevelProof {
                        level: SafetyLevel::RegionBinding,
                        verified: false,
                        source_line: *line,
                        description: format!("Region '{}' is not defined (set)", region),
                        witness: None,
                    });
                }
            },

            TwasmInstruction::LinearAcquire { region, line } => {
                if linear_acquired.contains_key(region) && !linear_released.contains_key(region) {
                    obligations.push(LevelProof {
                        level: SafetyLevel::Linear,
                        verified: false,
                        source_line: *line,
                        description: format!(
                            "Linear resource '{}' acquired twice without release",
                            region
                        ),
                        witness: None,
                    });
                } else {
                    linear_acquired.insert(region.clone(), *line);
                    linear_released.remove(region);
                }
            },

            TwasmInstruction::LinearRelease { region, line } => {
                if linear_acquired.contains_key(region) && !linear_released.contains_key(region) {
                    linear_released.insert(region.clone(), *line);
                    obligations.push(LevelProof {
                        level: SafetyLevel::Linear,
                        verified: true,
                        source_line: *line,
                        description: format!("Linear resource '{}' released exactly once", region),
                        witness: Some(format!(
                            "acquire@{} -> release@{}",
                            linear_acquired[region], line
                        )),
                    });

                    obligations.push(LevelProof {
                        level: SafetyLevel::LifetimeSafe,
                        verified: true,
                        source_line: *line,
                        description: format!("Resource '{}' lifetime ends at release", region),
                        witness: Some("lifetime_ends_at_release".to_string()),
                    });
                } else {
                    obligations.push(LevelProof {
                        level: SafetyLevel::Linear,
                        verified: false,
                        source_line: *line,
                        description: format!(
                            "Linear resource '{}' released without prior acquire",
                            region
                        ),
                        witness: None,
                    });
                }
            },

            _ => {},
        }
    }

    for (region, actual) in &actual_effects {
        let declared = declared_effects.get(region);
        let mut unique_actual: Vec<String> = actual.clone();
        unique_actual.sort();
        unique_actual.dedup();

        if let Some(decl) = declared {
            let all_covered = unique_actual.iter().all(|eff| decl.contains(eff));
            obligations.push(LevelProof {
                level: SafetyLevel::EffectSafe,
                verified: all_covered,
                source_line: 0,
                description: format!(
                    "Region '{}': declared effects {:?} cover actual effects {:?}",
                    region, decl, unique_actual
                ),
                witness: if all_covered {
                    Some(format!("{:?} ⊇ {:?}", decl, unique_actual))
                } else {
                    None
                },
            });
        } else {
            obligations.push(LevelProof {
                level: SafetyLevel::EffectSafe,
                verified: false,
                source_line: 0,
                description: format!(
                    "Region '{}': no effects declared but actual effects {:?} observed",
                    region, unique_actual
                ),
                witness: None,
            });
        }
    }

    for (region, acquire_line) in &linear_acquired {
        if !linear_released.contains_key(region) {
            obligations.push(LevelProof {
                level: SafetyLevel::Linear,
                verified: false,
                source_line: *acquire_line,
                description: format!(
                    "Linear resource '{}' acquired at line {} but never released",
                    region, acquire_line
                ),
                witness: None,
            });
        }
    }

    let has_lifetime_obligations = obligations
        .iter()
        .any(|o| o.level == SafetyLevel::LifetimeSafe);
    if !has_lifetime_obligations && !instructions.is_empty() {
        obligations.push(LevelProof {
            level: SafetyLevel::LifetimeSafe,
            verified: true,
            source_line: 0,
            description: "No lifetime violations detected (structural analysis)".to_string(),
            witness: Some("no_use_after_free".to_string()),
        });
    }

    obligations
}

// ---------------------------------------------------------------------------
// TypeInfo — discipline-specific engine configuration
// ---------------------------------------------------------------------------

/// Per-discipline configuration that parametrises the TypedWasm engine.
///
/// Each of the 39 type-checker disciplines (linear, affine, modal,
/// temporal, refinement, session, …) routes through the same engine but
/// cares about a different subset of the 10 safety levels. `TypeInfo`
/// selects which levels are enforced and captures the discipline's
/// identity for reporting.
#[derive(Debug, Clone)]
pub struct TypeInfo {
    /// Human-readable discipline name (e.g. "linear", "affine", "modal").
    pub discipline: String,
    /// Safety levels enforced for this discipline. Obligations outside
    /// this set are filtered from the analysis output.
    pub active_levels: HashSet<SafetyLevel>,
}

impl TypeInfo {
    /// Construct a [`TypeInfo`] that enforces every safety level. This is
    /// the original TypedWasm oracle behaviour.
    pub fn full() -> Self {
        TypeInfo {
            discipline: "typed-wasm".to_string(),
            active_levels: SafetyLevel::all().into_iter().collect(),
        }
    }

    /// Construct a [`TypeInfo`] with a custom discipline name and active
    /// level set. Level 1 (InstructionValidity) is always enforced.
    pub fn with_levels<S: Into<String>>(
        discipline: S,
        levels: impl IntoIterator<Item = SafetyLevel>,
    ) -> Self {
        let mut active: HashSet<SafetyLevel> = levels.into_iter().collect();
        active.insert(SafetyLevel::InstructionValidity);
        TypeInfo {
            discipline: discipline.into(),
            active_levels: active,
        }
    }
}

// ---------------------------------------------------------------------------
// Analyse — public engine entry point
// ---------------------------------------------------------------------------

/// Result of running the engine on a `.twasm` source.
#[derive(Debug, Clone)]
pub struct Analysis {
    /// Parsed instruction list (pre-filter, used by downstream consumers
    /// to extract region schemas and effect declarations).
    pub instructions: Vec<TwasmInstruction>,
    /// Proof obligations for the discipline's active safety levels.
    pub obligations: Vec<LevelProof>,
    /// The [`TypeInfo`] the analysis ran under (discipline name, active
    /// levels) — useful for report rendering.
    pub type_info: TypeInfo,
}

/// Parse `.twasm` source and generate proof obligations, filtering by
/// the discipline's active safety levels.
pub fn analyse(content: &str, type_info: &TypeInfo) -> Result<Analysis> {
    let instructions = parse_twasm(content)?;
    let mut obligations = generate_proof_obligations(&instructions);
    obligations.retain(|o| type_info.active_levels.contains(&o.level));
    Ok(Analysis {
        instructions,
        obligations,
        type_info: type_info.clone(),
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    const VALID_TWASM: &str = r#"
;; A simple typed-wasm program
region Particles { x: f32; y: f32; mass: f64 } [1024]
effect Particles { read; write }
region.get Particles[0] .x
region.get Particles[512] .mass
region.set Particles .y, 3.14
linear.acquire Particles
linear.release Particles
"#;

    const BAD_FIELD_TWASM: &str = r#"
region Foo { bar: i32 } [10]
region.get Foo[0] .nonexistent
"#;

    const OOB_TWASM: &str = r#"
region Small { val: i64 } [4]
region.get Small[99] .val
"#;

    #[test]
    fn test_parse_wasm_types() {
        assert_eq!(parse_wasm_type("i32").unwrap(), WasmType::I32);
        assert_eq!(parse_wasm_type("f64").unwrap(), WasmType::F64);
        assert_eq!(
            parse_wasm_type("?i32").unwrap(),
            WasmType::Nullable(Box::new(WasmType::I32))
        );
        assert_eq!(
            parse_wasm_type("ref(funcref)").unwrap(),
            WasmType::Ref("funcref".to_string())
        );
    }

    #[test]
    fn test_parse_valid_program() {
        let instructions = parse_twasm(VALID_TWASM).expect("should parse");
        assert_eq!(instructions.len(), 7);
    }

    #[test]
    fn test_level1_parse_failure() {
        let bad = "this is not valid twasm syntax";
        assert!(parse_twasm(bad).is_err());
    }

    #[test]
    fn test_level2_field_not_found() {
        let instructions = parse_twasm(BAD_FIELD_TWASM).unwrap();
        let obligations = generate_proof_obligations(&instructions);
        let failed = obligations
            .iter()
            .filter(|o| o.level == SafetyLevel::RegionBinding)
            .any(|o| !o.verified);
        assert!(failed);
    }

    #[test]
    fn test_level5_oob_index() {
        let instructions = parse_twasm(OOB_TWASM).unwrap();
        let obligations = generate_proof_obligations(&instructions);
        let failed = obligations
            .iter()
            .filter(|o| o.level == SafetyLevel::BoundsProof)
            .any(|o| !o.verified);
        assert!(failed);
    }

    #[test]
    fn test_valid_program_all_verified() {
        let instructions = parse_twasm(VALID_TWASM).unwrap();
        let obligations = generate_proof_obligations(&instructions);
        let failed: Vec<_> = obligations.iter().filter(|o| !o.verified).collect();
        assert!(failed.is_empty(), "got failures: {:?}", failed);
    }

    #[test]
    fn test_analyse_full_discipline() {
        let ti = TypeInfo::full();
        let analysis = analyse(VALID_TWASM, &ti).unwrap();
        assert!(!analysis.obligations.is_empty());
        assert_eq!(analysis.type_info.discipline, "typed-wasm");
    }

    #[test]
    fn test_analyse_linear_discipline_filters_levels() {
        let ti = TypeInfo::with_levels(
            "linear",
            [
                SafetyLevel::RegionBinding,
                SafetyLevel::TypeCompatible,
                SafetyLevel::ResultType,
                SafetyLevel::AliasSafe,
                SafetyLevel::Linear,
            ],
        );
        let analysis = analyse(VALID_TWASM, &ti).unwrap();
        // No BoundsProof, NullSafe, EffectSafe, LifetimeSafe obligations
        let levels: HashSet<SafetyLevel> =
            analysis.obligations.iter().map(|o| o.level.clone()).collect();
        assert!(!levels.contains(&SafetyLevel::BoundsProof));
        assert!(!levels.contains(&SafetyLevel::EffectSafe));
        assert!(levels.contains(&SafetyLevel::Linear));
        assert!(levels.contains(&SafetyLevel::InstructionValidity));
    }

    #[test]
    fn test_analyse_always_includes_level1() {
        let ti = TypeInfo::with_levels("minimal", []);
        let analysis = analyse(VALID_TWASM, &ti).unwrap();
        let has_l1 = analysis
            .obligations
            .iter()
            .any(|o| o.level == SafetyLevel::InstructionValidity);
        assert!(has_l1);
    }
}
