// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! The single wall-clock module: UTC "now", RFC 3339 strings and Unix seconds.
//!
//! Every timestamp in the crate comes through here, so the date library is
//! chosen in one place. The chosen library is `time`; `chrono` is unmaintained
//! (RUSTSEC-2026-0543) and is no longer a dependency.

use time::format_description::well_known::Rfc3339;
use time::OffsetDateTime;

/// The current instant, in UTC.
pub fn now() -> OffsetDateTime {
    OffsetDateTime::now_utc()
}

/// Format an instant as RFC 3339 (`2026-11-26T11:40:00.123456789Z`).
///
/// Formatting only fails for years outside 0000..=9999, which no clock reading
/// produces; the empty-string fallback keeps this infallible for callers.
pub fn to_rfc3339(t: OffsetDateTime) -> String {
    t.format(&Rfc3339).unwrap_or_default()
}

/// The current instant as an RFC 3339 string.
pub fn now_rfc3339() -> String {
    to_rfc3339(now())
}

/// Seconds since the Unix epoch.
pub fn unix_now() -> i64 {
    now().unix_timestamp()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rfc3339_round_trips_through_the_parser() {
        let t = now();
        let parsed = OffsetDateTime::parse(&to_rfc3339(t), &Rfc3339).expect("parse");
        assert_eq!(parsed, t);
    }

    #[test]
    fn rfc3339_is_utc_zulu() {
        assert!(now_rfc3339().ends_with('Z'));
    }

    #[test]
    fn unix_now_is_after_2026() {
        assert!(unix_now() > 1_767_225_600); // 2026-01-01T00:00:00Z
    }

    #[test]
    fn known_instant_formats_exactly() {
        let t = OffsetDateTime::from_unix_timestamp(0).expect("epoch");
        assert_eq!(to_rfc3339(t), "1970-01-01T00:00:00Z");
    }
}
