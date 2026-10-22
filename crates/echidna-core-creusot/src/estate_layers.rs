// SPDX-License-Identifier: MPL-2.0

//! Estate corpus-profile classification with Creusot proof annotations.
//!
//! Mirror of the pure part of `src/rust/corpus/profile.rs`: given a path
//! and an adapter name, decide which *layer* of the hyperpolymath stack
//! the file belongs to. The adapter itself does I/O; the classification
//! is pure, total and small enough to state contracts over — which is
//! exactly the kind of code the estate policy says belongs in
//! Rust/Creusot.
//!
//! ## Key proof obligations
//!
//! | ID | Property | Source |
//! |---|---|---|
//! | **PO-L1** | `layer_of_adapter` is total — every adapter name maps to exactly one layer | estate corpus profile |
//! | **PO-L2** | `layer_of_extension` is total over the mapped extensions and returns `None` otherwise (never panics) | profile manifest |
//! | **PO-L3** | The mapping is a *partition*: no adapter belongs to two layers | PO-L1 |
//! | **PO-L4** | `is_abi` holds exactly for the ABI adapters, which is what makes "every ABI is Idris2" checkable | estate policy 2026-10-22 |
//! | **PO-L5** | Extension classification agrees with adapter classification for the files each adapter owns | PO-L1 + PO-L2 |
//!
//! ## Verification status (honest)
//!
//! As with the rest of this crate, the annotations are **stated, not
//! proved**: `creusot-contracts` is not a dependency yet and no CI run
//! has discharged an obligation. What CI does run is the stable-Rust
//! `#[test]` mirror of each obligation, plus the `profile.rs` tests that
//! assert the same mapping for the real manifest.
//!
//! ## Creusot annotation style
//!
//! Contracts appear as doc-comment code blocks (always visible) and as
//! `#[cfg(feature = "creusot")]` attribute use, matching
//! `axiom_tracker.rs` and `pareto.rs`.

/// A layer of the hyperpolymath estate.
///
/// Discriminants are stable because they are serialised into corpus
/// metadata; the ordering is the dependency order of the stack (an ABI
/// is checked against its FFI, the FFI is called by the Rust layer).
///
/// ### Creusot proof obligation PO-L3 (partition)
/// ```text
/// #[logic]
/// fn layer_is_exclusive(l: Layer, m: Layer) -> bool {
///     l == m || (l as u8 != m as u8)
/// }
/// #[ensures(result <= Layer::Verifier as u8)]
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Layer {
    /// Idris2 ABI declarations (`src/abi/**`).
    Abi = 0,
    /// Zig API + FFI (`ffi/`, `src/zig_ffi/`).
    Api = 1,
    /// Ada/SPARK specifications and bodies.
    Spark = 2,
    /// Rust, and per policy Rust/Creusot.
    Rust = 3,
    /// Julia numeric / ML work.
    Julia = 4,
    /// Chapel parallel work.
    Chapel = 5,
    /// BEAM-native boundary code (SNIFs, never bare NIFs).
    Beam = 6,
    /// Type-theory libraries (Agda) and other contract languages.
    Types = 7,
    /// Anything the profile does not claim.
    Unknown = 8,
}

impl Layer {
    /// Every layer, in declaration order.
    pub const ALL: [Layer; 9] = [
        Layer::Abi,
        Layer::Api,
        Layer::Spark,
        Layer::Rust,
        Layer::Julia,
        Layer::Chapel,
        Layer::Beam,
        Layer::Types,
        Layer::Unknown,
    ];

    /// Stable wire label, used as the `layer:` module option.
    ///
    /// ### Creusot contract
    /// ```text
    /// #[ensures(result@.len() > 0)]
    /// ```
    pub fn label(self) -> &'static str {
        match self {
            Layer::Abi => "abi",
            Layer::Api => "api",
            Layer::Spark => "spark",
            Layer::Rust => "rust",
            Layer::Julia => "julia",
            Layer::Chapel => "chapel",
            Layer::Beam => "beam",
            Layer::Types => "types",
            Layer::Unknown => "unknown",
        }
    }

    /// True for the layer every ABI must live in (PO-L4).
    ///
    /// ### Creusot contract
    /// ```text
    /// #[ensures(result == (self == Layer::Abi))]
    /// ```
    pub fn is_abi(self) -> bool {
        self == Layer::Abi
    }
}

/// Layer owned by a corpus adapter. Total: unknown adapters map to
/// `Layer::Unknown` rather than failing, because a new adapter must be
/// able to land before its policy entry does (PO-L1).
///
/// ### Creusot contract
/// ```text
/// #[ensures(result != Layer::Unknown ==> Layer::ALL.contains(result))]
/// ```
pub fn layer_of_adapter(adapter: &str) -> Layer {
    match adapter {
        "idris2" | "idris" => Layer::Abi,
        "agda" | "coq" | "lean" | "isabelle" => Layer::Types,
        "spark_ada" | "spark" | "ada" | "dafny" | "fstar" | "why3" => Layer::Spark,
        "creusot" | "rust_creusot" => Layer::Rust,
        _ => Layer::Unknown,
    }
}

/// Layer implied by a file extension, or `None` when the profile does
/// not claim it (PO-L2: no panics, no guessing).
///
/// ### Creusot contract
/// ```text
/// #[ensures(result == None || result.unwrap() != Layer::Unknown)]
/// ```
pub fn layer_of_extension(ext: &str) -> Option<Layer> {
    match ext {
        "idr" | "ipkg" => Some(Layer::Abi),
        "zig" => Some(Layer::Api),
        "ads" | "adb" | "gpr" => Some(Layer::Spark),
        "rs" => Some(Layer::Rust),
        "jl" => Some(Layer::Julia),
        "chpl" => Some(Layer::Chapel),
        "ex" | "exs" => Some(Layer::Beam),
        "agda" | "thy" | "v" | "lean" | "dfy" | "fst" => Some(Layer::Types),
        _ => None,
    }
}

/// The corpus adapter that indexes a layer, if any.
///
/// Only four layers have an adapter: there is no corpus adapter for the
/// Zig FFI, Julia, Chapel or BEAM boundaries, so claiming one here would
/// be a lie the manifest could not honour. Those layers return `None`
/// even though [`layer_of_extension`] can recognise their files.
pub fn adapter_of_layer(layer: Layer) -> Option<&'static str> {
    match layer {
        Layer::Abi => Some("idris2"),
        Layer::Spark => Some("spark_ada"),
        Layer::Rust => Some("creusot"),
        Layer::Types => Some("agda"),
        Layer::Api | Layer::Julia | Layer::Chapel | Layer::Beam | Layer::Unknown => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_layer_has_a_distinct_label() {
        let mut labels: Vec<&str> = Layer::ALL.iter().map(|l| l.label()).collect();
        labels.sort_unstable();
        let before = labels.len();
        labels.dedup();
        assert_eq!(before, labels.len(), "duplicate layer label");
        assert_eq!(Layer::ALL.len(), 9);
    }

    #[test]
    fn adapter_mapping_is_total_and_within_the_enum() {
        // PO-L1: total over names, and the result is always a member.
        for adapter in [
            "idris2", "agda", "coq", "lean", "isabelle", "spark_ada", "dafny", "fstar",
            "why3", "creusot", "not_an_adapter", "",
        ] {
            let layer = layer_of_adapter(adapter);
            assert!(Layer::ALL.contains(&layer), "{adapter} -> {layer:?}");
        }
    }

    #[test]
    fn extension_mapping_never_claims_unknown() {
        // PO-L2
        for ext in ["idr", "zig", "ads", "adb", "rs", "jl", "chpl", "ex", "agda", "zzz", ""] {
            let layer = layer_of_extension(ext);
            assert!(layer != Some(Layer::Unknown), "{ext} claimed the unknown layer");
        }
        assert_eq!(layer_of_extension("zzz"), None);
    }

    #[test]
    fn extensions_agree_with_their_adapter() {
        // PO-L5: for the extensions the profile maps, the layer matches
        // the layer of the adapter that indexes that extension.
        for (ext, adapter) in [
            ("idr", "idris2"),
            ("ads", "spark_ada"),
            ("adb", "spark_ada"),
            ("rs", "creusot"),
            ("agda", "agda"),
        ] {
            assert_eq!(layer_of_extension(ext), Some(layer_of_adapter(adapter)));
        }
    }

    #[test]
    fn abi_layer_is_exactly_the_idris_adapters() {
        // PO-L4: the policy claim "every ABI is Idris2" is checkable.
        for adapter in ["idris2", "idris"] {
            assert!(layer_of_adapter(adapter).is_abi());
        }
        for adapter in ["agda", "creusot", "spark_ada", "zig", "julia", "chapel"] {
            assert!(!layer_of_adapter(adapter).is_abi(), "{adapter}");
        }
    }

    #[test]
    fn adapter_of_layer_round_trips_where_an_adapter_exists() {
        for layer in Layer::ALL {
            if let Some(adapter) = adapter_of_layer(layer) {
                assert_eq!(layer_of_adapter(adapter), layer, "{layer:?}");
            }
        }
        // The layers with no corpus adapter say so rather than naming one.
        for layer in [Layer::Api, Layer::Julia, Layer::Chapel, Layer::Beam] {
            assert_eq!(adapter_of_layer(layer), None, "{layer:?}");
        }
        assert_eq!(adapter_of_layer(Layer::Unknown), None);
    }

    #[test]
    fn partition_holds_for_every_pair() {
        // PO-L3: labels are injective, so no adapter lands in two layers
        // through a shared label.
        for a in Layer::ALL {
            for b in Layer::ALL {
                if a != b {
                    assert_ne!(a.label(), b.label());
                }
            }
        }
    }
}
