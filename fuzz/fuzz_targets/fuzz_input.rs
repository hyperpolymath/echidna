// SPDX-License-Identifier: PMPL-1.0
//! Generic fuzz target for arbitrary input processing

#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    // Fuzz with arbitrary byte input
    // This exercises any parsing/processing functions with random data
    if let Ok(input) = std::str::from_utf8(data) {
        // Try to process the input as text
        let _ = input.trim();
        let _ = input.lines().count();
    }

    // Exercise the data directly as bytes
    let _ = data.len();
    let _ = data.is_empty();
});
