// SPDX-License-Identifier: PMPL-1.0-or-later
// GraphQL FFI Wrapper - Connects GraphQL interface to ECHIDNA Rust core via Zig FFI

use std::ffi::{CString, CStr};
use std::os::raw::{c_char, c_int};
use anyhow::{Result, anyhow};

// Re-export FFI types from core
pub use echidna::ffi::{FfiStatus, FfiStringSlice, FfiOwnedString, FfiProverConfig};

// External Zig FFI functions (from libechidna_ffi.so)
extern "C" {
    pub fn echidna_init() -> c_int;
    pub fn echidna_deinit();
    pub fn echidna_create_prover(kind: u8) -> c_int;
    pub fn echidna_destroy_prover(handle: c_int);
    pub fn echidna_parse_string(handle: c_int, content: *const u8, len: usize) -> c_int;
    pub fn echidna_verify_proof(handle: c_int) -> c_int;
    pub fn echidna_apply_tactic(handle: c_int, tactic: *const u8, len: usize) -> c_int;
    pub fn echidna_suggest_tactics(handle: c_int, limit: c_int, out: *mut u8, out_len: *mut usize) -> c_int;
    pub fn echidna_export_proof(handle: c_int, out: *mut u8, out_len: *mut usize) -> c_int;
    pub fn echidna_last_error() -> *const u8;
    pub fn echidna_version() -> *const u8;
}

/// Initialize the FFI layer
pub fn init_ffi() -> Result<()> {
    unsafe {
        let rc = echidna_init();
        if rc != 0 {
            let err_ptr = echidna_last_error();
            let err_msg = if err_ptr.is_null() {
                "Unknown FFI initialization error".to_string()
            } else {
                CStr::from_ptr(err_ptr as *const c_char).to_string_lossy().into_owned()
            };
            return Err(anyhow!("FFI initialization failed: {}", err_msg));
        }
    }
    Ok(())
}

/// Get FFI version
pub fn get_version() -> Result<String> {
    unsafe {
        let ptr = echidna_version();
        if ptr.is_null() {
            return Err(anyhow!("FFI version pointer is null"));
        }
        let version = CStr::from_ptr(ptr as *const c_char).to_string_lossy().into_owned();
        Ok(version)
    }
}

/// Get last FFI error
pub fn get_last_error() -> Result<String> {
    unsafe {
        let ptr = echidna_last_error();
        if ptr.is_null() {
            return Err(anyhow!("No error message available"));
        }
        let error = CStr::from_ptr(ptr as *const c_char).to_string_lossy().into_owned();
        Ok(error)
    }
}

/// Create a prover instance via FFI
pub fn create_prover(prover_kind: u8) -> Result<i32> {
    unsafe {
        let handle = echidna_create_prover(prover_kind);
        if handle < 0 {
            let error = get_last_error()?;
            return Err(anyhow!("Failed to create prover: {}", error));
        }
        Ok(handle)
    }
}

/// Destroy a prover instance
pub fn destroy_prover(handle: i32) -> Result<()> {
    unsafe {
        echidna_destroy_prover(handle);
    }
    Ok(())
}

/// Parse proof content via FFI
pub fn parse_string(handle: i32, content: &str) -> Result<()> {
    unsafe {
        let c_content = CString::new(content)?;
        let rc = echidna_parse_string(handle, c_content.as_ptr() as *const u8, content.len());
        if rc != 0 {
            let error = get_last_error()?;
            return Err(anyhow!("Parse failed: {}", error));
        }
    }
    Ok(())
}

/// Verify proof via FFI
pub fn verify_proof(handle: i32) -> Result<bool> {
    unsafe {
        let rc = echidna_verify_proof(handle);
        Ok(rc == 1)
    }
}

/// Apply tactic via FFI
pub fn apply_tactic(handle: i32, tactic: &str) -> Result<bool> {
    unsafe {
        let c_tactic = CString::new(tactic)?;
        let rc = echidna_apply_tactic(handle, c_tactic.as_ptr() as *const u8, tactic.len());
        Ok(rc == 0)
    }
}

/// Suggest tactics via FFI
pub fn suggest_tactics(handle: i32, limit: usize) -> Result<Vec<String>> {
    unsafe {
        let mut buffer = vec![0u8; 4096];
        let mut buffer_len = buffer.len();
        
        let rc = echidna_suggest_tactics(
            handle,
            limit as c_int,
            buffer.as_mut_ptr(),
            &mut buffer_len as *mut usize
        );
        
        if rc != 0 {
            let error = get_last_error()?;
            return Err(anyhow!("Suggest tactics failed: {}", error));
        }
        
        if buffer_len == 0 {
            return Ok(vec![]);
        }
        
        buffer.truncate(buffer_len);
        let result = String::from_utf8(buffer)?;
        
        // Parse JSON array of tactics
        let tactics: Vec<String> = serde_json::from_str(&result)?;
        Ok(tactics)
    }
}

/// Export proof via FFI
pub fn export_proof(handle: i32) -> Result<String> {
    unsafe {
        let mut buffer = vec![0u8; 8192];
        let mut buffer_len = buffer.len();
        
        let rc = echidna_export_proof(
            handle,
            buffer.as_mut_ptr(),
            &mut buffer_len as *mut usize
        );
        
        if rc != 0 {
            let error = get_last_error()?;
            return Err(anyhow!("Export failed: {}", error));
        }
        
        if buffer_len == 0 {
            return Ok(String::new());
        }
        
        buffer.truncate(buffer_len);
        let result = String::from_utf8(buffer)?;
        Ok(result)
    }
}

/// Convert GraphQL ProverKind to FFI ordinal
pub fn prover_kind_to_ffi(kind: &crate::schema::ProverKind) -> u8 {
    match kind {
        crate::schema::ProverKind::Agda => 0,
        crate::schema::ProverKind::Coq => 1,
        crate::schema::ProverKind::Lean => 2,
        crate::schema::ProverKind::Isabelle => 3,
        crate::schema::ProverKind::Z3 => 4,
        crate::schema::ProverKind::CVC5 => 5,
        crate::schema::ProverKind::Metamath => 6,
        crate::schema::ProverKind::HOLLight => 7,
        crate::schema::ProverKind::Mizar => 8,
        crate::schema::ProverKind::PVS => 9,
        crate::schema::ProverKind::ACL2 => 10,
        crate::schema::ProverKind::HOL4 => 11,
        crate::schema::ProverKind::Idris2 => 12,
        crate::schema::ProverKind::Vampire => 13,
        crate::schema::ProverKind::EProver => 14,
        crate::schema::ProverKind::SPASS => 15,
        crate::schema::ProverKind::AltErgo => 16,
        crate::schema::ProverKind::FStar => 17,
        crate::schema::ProverKind::Dafny => 18,
        crate::schema::ProverKind::Why3 => 19,
        crate::schema::ProverKind::TLAPS => 20,
        crate::schema::ProverKind::Twelf => 21,
        crate::schema::ProverKind::Nuprl => 22,
        crate::schema::ProverKind::Minlog => 23,
        crate::schema::ProverKind::Imandra => 24,
        crate::schema::ProverKind::GLPK => 25,
        crate::schema::ProverKind::SCIP => 26,
        crate::schema::ProverKind::MiniZinc => 27,
        crate::schema::ProverKind::Chuffed => 28,
        crate::schema::ProverKind::ORTools => 29,
        crate::schema::ProverKind::Lean3 => 30,
        crate::schema::ProverKind::TypedWasm => 31,
        crate::schema::ProverKind::SPIN => 32,
        crate::schema::ProverKind::CBMC => 33,
        crate::schema::ProverKind::SeaHorn => 34,
        crate::schema::ProverKind::CaDiCaL => 35,
        crate::schema::ProverKind::Kissat => 36,
        crate::schema::ProverKind::MiniSat => 37,
        crate::schema::ProverKind::NuSMV => 38,
        crate::schema::ProverKind::TLC => 39,
        crate::schema::ProverKind::Alloy => 40,
        crate::schema::ProverKind::Prism => 41,
        crate::schema::ProverKind::UPPAAL => 42,
        crate::schema::ProverKind::FramaC => 43,
        crate::schema::ProverKind::Viper => 44,
        crate::schema::ProverKind::Tamarin => 45,
        crate::schema::ProverKind::ProVerif => 46,
        crate::schema::ProverKind::KeY => 47,
        crate::schema::ProverKind::DReal => 48,
        crate::schema::ProverKind::ABC => 49,
        crate::schema::ProverKind::TypeLL => 50,
        crate::schema::ProverKind::KatagoriaVerifier => 51,
        crate::schema::ProverKind::TropicalTypeChecker => 52,
        crate::schema::ProverKind::ChoreographicTypeChecker => 53,
        crate::schema::ProverKind::EpistemicTypeChecker => 54,
        crate::schema::ProverKind::EchoTypeChecker => 55,
        crate::schema::ProverKind::SessionTypeChecker => 56,
        crate::schema::ProverKind::ModalTypeChecker => 57,
        crate::schema::ProverKind::QTTTypeChecker => 58,
        crate::schema::ProverKind::EffectRowTypeChecker => 59,
        crate::schema::ProverKind::DependentTypeChecker => 60,
        crate::schema::ProverKind::RefinementTypeChecker => 61,
        crate::schema::ProverKind::OrdinaryTypeChecker => 62,
        crate::schema::ProverKind::PhantomTypeChecker => 63,
        crate::schema::ProverKind::PolymorphicTypeChecker => 64,
        crate::schema::ProverKind::ExistentialTypeChecker => 65,
        crate::schema::ProverKind::HigherKindedTypeChecker => 66,
        crate::schema::ProverKind::RowTypeChecker => 67,
        crate::schema::ProverKind::SubtypingTypeChecker => 68,
        crate::schema::ProverKind::IntersectionTypeChecker => 69,
        crate::schema::ProverKind::UnionTypeChecker => 70,
        crate::schema::ProverKind::GradualTypeChecker => 71,
        crate::schema::ProverKind::HoareTypeChecker => 72,
        crate::schema::ProverKind::IndexedTypeChecker => 73,
        crate::schema::ProverKind::LinearTypeChecker => 74,
        crate::schema::ProverKind::AffineTypeChecker => 75,
        crate::schema::ProverKind::RelevantTypeChecker => 76,
        crate::schema::ProverKind::OrderedTypeChecker => 77,
        crate::schema::ProverKind::UniquenessTypeChecker => 78,
        crate::schema::ProverKind::ImmutableTypeChecker => 79,
        crate::schema::ProverKind::CapabilityTypeChecker => 80,
        crate::schema::ProverKind::BunchedTypeChecker => 81,
        crate::schema::ProverKind::TemporalTypeChecker => 82,
        crate::schema::ProverKind::ProvabilityTypeChecker => 83,
        crate::schema::ProverKind::ImpureTypeChecker => 84,
        crate::schema::ProverKind::CoeffectTypeChecker => 85,
        crate::schema::ProverKind::ProbabilisticTypeChecker => 86,
        crate::schema::ProverKind::DyadicTypeChecker => 87,
        crate::schema::ProverKind::HomotopyTypeChecker => 88,
        crate::schema::ProverKind::CubicalTypeChecker => 89,
        crate::schema::ProverKind::NominalTypeChecker => 90,
        crate::schema::ProverKind::Abella => 91,
        crate::schema::ProverKind::Dedukti => 92,
        crate::schema::ProverKind::Cameleer => 93,
        crate::schema::ProverKind::ACL2s => 94,
        crate::schema::ProverKind::IsabelleZF => 95,
        crate::schema::ProverKind::Boogie => 96,
        crate::schema::ProverKind::Naproche => 97,
        crate::schema::ProverKind::Matita => 98,
        crate::schema::ProverKind::Arend => 99,
        crate::schema::ProverKind::Athena => 100,
        crate::schema::ProverKind::LambdaProlog => 101,
        crate::schema::ProverKind::Mercury => 102,
        crate::schema::ProverKind::Nitpick => 103,
        crate::schema::ProverKind::Nunchaku => 104,
        crate::schema::ProverKind::CubicalAgda => 105,
        crate::schema::ProverKind::Zipperposition => 106,
        crate::schema::ProverKind::Prover9 => 107,
        crate::schema::ProverKind::OpenSmt => 108,
        crate::schema::ProverKind::SmtRat => 109,
        crate::schema::ProverKind::Rocq => 110,
        crate::schema::ProverKind::UppaalStratego => 111,
        crate::schema::ProverKind::MizAR => 112,
        crate::schema::ProverKind::GPUVerify => 113,
        crate::schema::ProverKind::Faial => 114,
        crate::schema::ProverKind::Leo3 => 115,
        crate::schema::ProverKind::Satallax => 116,
        crate::schema::ProverKind::Lash => 117,
        crate::schema::ProverKind::AgsyHOL => 118,
        crate::schema::ProverKind::IProver => 119,
        crate::schema::ProverKind::Princess => 120,
        crate::schema::ProverKind::Twee => 121,
        crate::schema::ProverKind::MetiTarski => 122,
        crate::schema::ProverKind::CSI => 123,
        crate::schema::ProverKind::AProVE => 124,
        crate::schema::ProverKind::GNATprove => 125,
        crate::schema::ProverKind::Stainless => 126,
        crate::schema::ProverKind::LiquidHaskell => 127,
        crate::schema::ProverKind::KeYmaeraX => 128,
        crate::schema::ProverKind::Qepcad => 129,
        crate::schema::ProverKind::Redlog => 130,
        crate::schema::ProverKind::MleanCoP => 131,
        crate::schema::ProverKind::IleanCoP => 132,
        crate::schema::ProverKind::NanoCoP => 133,
        crate::schema::ProverKind::MetTeL2 => 134,
        crate::schema::ProverKind::ELK => 135,
        crate::schema::ProverKind::Konclude => 136,
        crate::schema::ProverKind::Storm => 137,
        crate::schema::ProverKind::ProB => 138,
        crate::schema::ProverKind::EasyCrypt => 139,
        crate::schema::ProverKind::CryptoVerif => 140,
    }
}

/// Convert FFI ordinal to GraphQL ProverKind
pub fn ffi_to_prover_kind(ordinal: u8) -> Option<crate::schema::ProverKind> {
    match ordinal {
        0 => Some(crate::schema::ProverKind::Agda),
        1 => Some(crate::schema::ProverKind::Coq),
        2 => Some(crate::schema::ProverKind::Lean),
        3 => Some(crate::schema::ProverKind::Isabelle),
        4 => Some(crate::schema::ProverKind::Z3),
        5 => Some(crate::schema::ProverKind::CVC5),
        6 => Some(crate::schema::ProverKind::Metamath),
        7 => Some(crate::schema::ProverKind::HOLLight),
        8 => Some(crate::schema::ProverKind::Mizar),
        9 => Some(crate::schema::ProverKind::PVS),
        10 => Some(crate::schema::ProverKind::ACL2),
        11 => Some(crate::schema::ProverKind::HOL4),
        12 => Some(crate::schema::ProverKind::Idris2),
        13 => Some(crate::schema::ProverKind::Vampire),
        14 => Some(crate::schema::ProverKind::EProver),
        15 => Some(crate::schema::ProverKind::SPASS),
        16 => Some(crate::schema::ProverKind::AltErgo),
        17 => Some(crate::schema::ProverKind::FStar),
        18 => Some(crate::schema::ProverKind::Dafny),
        19 => Some(crate::schema::ProverKind::Why3),
        20 => Some(crate::schema::ProverKind::TLAPS),
        21 => Some(crate::schema::ProverKind::Twelf),
        22 => Some(crate::schema::ProverKind::Nuprl),
        23 => Some(crate::schema::ProverKind::Minlog),
        24 => Some(crate::schema::ProverKind::Imandra),
        25 => Some(crate::schema::ProverKind::GLPK),
        26 => Some(crate::schema::ProverKind::SCIP),
        27 => Some(crate::schema::ProverKind::MiniZinc),
        28 => Some(crate::schema::ProverKind::Chuffed),
        29 => Some(crate::schema::ProverKind::ORTools),
        30 => Some(crate::schema::ProverKind::Lean3),
        31 => Some(crate::schema::ProverKind::TypedWasm),
        32 => Some(crate::schema::ProverKind::SPIN),
        33 => Some(crate::schema::ProverKind::CBMC),
        34 => Some(crate::schema::ProverKind::SeaHorn),
        35 => Some(crate::schema::ProverKind::CaDiCaL),
        36 => Some(crate::schema::ProverKind::Kissat),
        37 => Some(crate::schema::ProverKind::MiniSat),
        38 => Some(crate::schema::ProverKind::NuSMV),
        39 => Some(crate::schema::ProverKind::TLC),
        40 => Some(crate::schema::ProverKind::Alloy),
        41 => Some(crate::schema::ProverKind::Prism),
        42 => Some(crate::schema::ProverKind::UPPAAL),
        43 => Some(crate::schema::ProverKind::FramaC),
        44 => Some(crate::schema::ProverKind::Viper),
        45 => Some(crate::schema::ProverKind::Tamarin),
        46 => Some(crate::schema::ProverKind::ProVerif),
        47 => Some(crate::schema::ProverKind::KeY),
        48 => Some(crate::schema::ProverKind::DReal),
        49 => Some(crate::schema::ProverKind::ABC),
        50 => Some(crate::schema::ProverKind::TypeLL),
        51 => Some(crate::schema::ProverKind::KatagoriaVerifier),
        52 => Some(crate::schema::ProverKind::TropicalTypeChecker),
        53 => Some(crate::schema::ProverKind::ChoreographicTypeChecker),
        54 => Some(crate::schema::ProverKind::EpistemicTypeChecker),
        55 => Some(crate::schema::ProverKind::EchoTypeChecker),
        56 => Some(crate::schema::ProverKind::SessionTypeChecker),
        57 => Some(crate::schema::ProverKind::ModalTypeChecker),
        58 => Some(crate::schema::ProverKind::QTTTypeChecker),
        59 => Some(crate::schema::ProverKind::EffectRowTypeChecker),
        60 => Some(crate::schema::ProverKind::DependentTypeChecker),
        61 => Some(crate::schema::ProverKind::RefinementTypeChecker),
        62 => Some(crate::schema::ProverKind::OrdinaryTypeChecker),
        63 => Some(crate::schema::ProverKind::PhantomTypeChecker),
        64 => Some(crate::schema::ProverKind::PolymorphicTypeChecker),
        65 => Some(crate::schema::ProverKind::ExistentialTypeChecker),
        66 => Some(crate::schema::ProverKind::HigherKindedTypeChecker),
        67 => Some(crate::schema::ProverKind::RowTypeChecker),
        68 => Some(crate::schema::ProverKind::SubtypingTypeChecker),
        69 => Some(crate::schema::ProverKind::IntersectionTypeChecker),
        70 => Some(crate::schema::ProverKind::UnionTypeChecker),
        71 => Some(crate::schema::ProverKind::GradualTypeChecker),
        72 => Some(crate::schema::ProverKind::HoareTypeChecker),
        73 => Some(crate::schema::ProverKind::IndexedTypeChecker),
        74 => Some(crate::schema::ProverKind::LinearTypeChecker),
        75 => Some(crate::schema::ProverKind::AffineTypeChecker),
        76 => Some(crate::schema::ProverKind::RelevantTypeChecker),
        77 => Some(crate::schema::ProverKind::OrderedTypeChecker),
        78 => Some(crate::schema::ProverKind::UniquenessTypeChecker),
        79 => Some(crate::schema::ProverKind::ImmutableTypeChecker),
        80 => Some(crate::schema::ProverKind::CapabilityTypeChecker),
        81 => Some(crate::schema::ProverKind::BunchedTypeChecker),
        82 => Some(crate::schema::ProverKind::TemporalTypeChecker),
        83 => Some(crate::schema::ProverKind::ProvabilityTypeChecker),
        84 => Some(crate::schema::ProverKind::ImpureTypeChecker),
        85 => Some(crate::schema::ProverKind::CoeffectTypeChecker),
        86 => Some(crate::schema::ProverKind::ProbabilisticTypeChecker),
        87 => Some(crate::schema::ProverKind::DyadicTypeChecker),
        88 => Some(crate::schema::ProverKind::HomotopyTypeChecker),
        89 => Some(crate::schema::ProverKind::CubicalTypeChecker),
        90 => Some(crate::schema::ProverKind::NominalTypeChecker),
        91 => Some(crate::schema::ProverKind::Abella),
        92 => Some(crate::schema::ProverKind::Dedukti),
        93 => Some(crate::schema::ProverKind::Cameleer),
        94 => Some(crate::schema::ProverKind::ACL2s),
        95 => Some(crate::schema::ProverKind::IsabelleZF),
        96 => Some(crate::schema::ProverKind::Boogie),
        97 => Some(crate::schema::ProverKind::Naproche),
        98 => Some(crate::schema::ProverKind::Matita),
        99 => Some(crate::schema::ProverKind::Arend),
        100 => Some(crate::schema::ProverKind::Athena),
        101 => Some(crate::schema::ProverKind::LambdaProlog),
        102 => Some(crate::schema::ProverKind::Mercury),
        103 => Some(crate::schema::ProverKind::Nitpick),
        104 => Some(crate::schema::ProverKind::Nunchaku),
        105 => Some(crate::schema::ProverKind::CubicalAgda),
        106 => Some(crate::schema::ProverKind::Zipperposition),
        107 => Some(crate::schema::ProverKind::Prover9),
        108 => Some(crate::schema::ProverKind::OpenSmt),
        109 => Some(crate::schema::ProverKind::SmtRat),
        110 => Some(crate::schema::ProverKind::Rocq),
        111 => Some(crate::schema::ProverKind::UppaalStratego),
        112 => Some(crate::schema::ProverKind::MizAR),
        113 => Some(crate::schema::ProverKind::GPUVerify),
        114 => Some(crate::schema::ProverKind::Faial),
        115 => Some(crate::schema::ProverKind::Leo3),
        116 => Some(crate::schema::ProverKind::Satallax),
        117 => Some(crate::schema::ProverKind::Lash),
        118 => Some(crate::schema::ProverKind::AgsyHOL),
        119 => Some(crate::schema::ProverKind::IProver),
        120 => Some(crate::schema::ProverKind::Princess),
        121 => Some(crate::schema::ProverKind::Twee),
        122 => Some(crate::schema::ProverKind::MetiTarski),
        123 => Some(crate::schema::ProverKind::CSI),
        124 => Some(crate::schema::ProverKind::AProVE),
        125 => Some(crate::schema::ProverKind::GNATprove),
        126 => Some(crate::schema::ProverKind::Stainless),
        127 => Some(crate::schema::ProverKind::LiquidHaskell),
        128 => Some(crate::schema::ProverKind::KeYmaeraX),
        129 => Some(crate::schema::ProverKind::Qepcad),
        130 => Some(crate::schema::ProverKind::Redlog),
        131 => Some(crate::schema::ProverKind::MleanCoP),
        132 => Some(crate::schema::ProverKind::IleanCoP),
        133 => Some(crate::schema::ProverKind::NanoCoP),
        134 => Some(crate::schema::ProverKind::MetTeL2),
        135 => Some(crate::schema::ProverKind::ELK),
        136 => Some(crate::schema::ProverKind::Konclude),
        137 => Some(crate::schema::ProverKind::Storm),
        138 => Some(crate::schema::ProverKind::ProB),
        139 => Some(crate::schema::ProverKind::EasyCrypt),
        140 => Some(crate::schema::ProverKind::CryptoVerif),
        _ => None,
    }
}
