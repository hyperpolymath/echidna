// SPDX-License-Identifier: PMPL-1.0-or-later
//! Fuzz target for configuration parsing

#![no_main]

use libfuzzer_sys::fuzz_target;
use serde::Deserialize;

/// Configuration structure matching echidnabot's Config
/// (Re-defined here to avoid needing full lib dependencies)
#[derive(Debug, Deserialize)]
struct Config {
    #[serde(default)]
    server: Option<ServerConfig>,
    #[serde(default)]
    database: Option<DatabaseConfig>,
    #[serde(default)]
    echidna: Option<EchidnaConfig>,
    #[serde(default)]
    github: Option<GitHubConfig>,
    #[serde(default)]
    scheduler: Option<SchedulerConfig>,
}

#[derive(Debug, Deserialize)]
struct ServerConfig {
    host: Option<String>,
    port: Option<u16>,
}

#[derive(Debug, Deserialize)]
struct DatabaseConfig {
    url: Option<String>,
    max_connections: Option<u32>,
}

#[derive(Debug, Deserialize)]
struct EchidnaConfig {
    endpoint: Option<String>,
    timeout_secs: Option<u64>,
}

#[derive(Debug, Deserialize)]
struct GitHubConfig {
    app_id: Option<u64>,
    private_key_path: Option<String>,
    token: Option<String>,
    webhook_secret: Option<String>,
}

#[derive(Debug, Deserialize)]
struct SchedulerConfig {
    max_concurrent: Option<usize>,
    queue_size: Option<usize>,
}

fuzz_target!(|data: &[u8]| {
    // Try to parse as TOML configuration
    if let Ok(input) = std::str::from_utf8(data) {
        // Fuzz TOML parsing
        let _ = toml::from_str::<Config>(input);

        // Also try parsing as individual sections
        let _ = toml::from_str::<ServerConfig>(input);
        let _ = toml::from_str::<DatabaseConfig>(input);
        let _ = toml::from_str::<EchidnaConfig>(input);
        let _ = toml::from_str::<GitHubConfig>(input);
        let _ = toml::from_str::<SchedulerConfig>(input);
    }
});
