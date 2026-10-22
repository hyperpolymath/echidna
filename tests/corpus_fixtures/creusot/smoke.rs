// SPDX-License-Identifier: MPL-2.0
// Smoke fixture for the creusot corpus adapter.
//
// Covers: a function with requires/ensures, a #[trusted] function (which
// the adapter must report as a postulate), a #[logic] ghost definition
// using pearlite!, and a struct.

use creusot_contracts::*;

#[requires(x@ < 1000)]
#[ensures(result@ == x@ + 1)]
pub fn increment(x: u32) -> u32 {
    x + 1
}

#[trusted]
#[requires(n@ > 0)]
#[ensures(result@ == n@)]
pub fn trusted_identity(n: u32) -> u32 {
    n
}

#[logic]
pub fn double(x: Int) -> Int {
    pearlite! { x * 2 }
}

pub struct Counter {
    value: u32,
}

#[test]
fn not_part_of_the_proved_surface() {
    assert_eq!(increment(1), 2);
}
