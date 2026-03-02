//! Configuration management for echidnabot

use serde::Deserialize;
use std::path::Path;

use crate::error::Result;

/// Main configuration structure
#[derive(Debug, Deserialize, Clone)]
pub struct Config {
    /// Server configuration
    #[serde(default)]
    pub server: ServerConfig,

    /// Database configuration
    #[serde(default)]
    pub database: DatabaseConfig,

    /// ECHIDNA Core connection
    #[serde(default)]
    pub echidna: EchidnaConfig,

    /// GitHub integration
    #[serde(default)]
    pub github: Option<GitHubConfig>,

    /// GitLab integration
    #[serde(default)]
    pub gitlab: Option<GitLabConfig>,

    /// Scheduler configuration
    #[serde(default)]
    pub scheduler: SchedulerConfig,
}

#[derive(Debug, Deserialize, Clone, Copy)]
#[serde(rename_all = "lowercase")]
pub enum EchidnaApiMode {
    Auto,
    Graphql,
    Rest,
}

#[derive(Debug, Deserialize, Clone)]
pub struct ServerConfig {
    #[serde(default = "default_host")]
    pub host: String,

    #[serde(default = "default_port")]
    pub port: u16,
}

impl Default for ServerConfig {
    fn default() -> Self {
        Self {
            host: default_host(),
            port: default_port(),
        }
    }
}

fn default_host() -> String {
    "0.0.0.0".to_string()
}

fn default_port() -> u16 {
    8080
}

#[derive(Debug, Deserialize, Clone)]
pub struct DatabaseConfig {
    #[serde(default = "default_database_url")]
    pub url: String,

    #[serde(default = "default_max_connections")]
    pub max_connections: u32,
}

impl Default for DatabaseConfig {
    fn default() -> Self {
        Self {
            url: default_database_url(),
            max_connections: default_max_connections(),
        }
    }
}

fn default_database_url() -> String {
    "sqlite://echidnabot.db".to_string()
}

fn default_max_connections() -> u32 {
    5
}

#[derive(Debug, Deserialize, Clone)]
pub struct EchidnaConfig {
    /// ECHIDNA Core GraphQL endpoint
    #[serde(default = "default_echidna_endpoint")]
    pub endpoint: String,

    /// ECHIDNA Core REST endpoint
    #[serde(default = "default_echidna_rest_endpoint")]
    pub rest_endpoint: String,

    /// API mode (auto, graphql, rest)
    #[serde(default = "default_echidna_mode")]
    pub mode: EchidnaApiMode,

    /// Timeout for proof verification (seconds)
    #[serde(default = "default_timeout")]
    pub timeout_secs: u64,
}

impl Default for EchidnaConfig {
    fn default() -> Self {
        Self {
            endpoint: default_echidna_endpoint(),
            rest_endpoint: default_echidna_rest_endpoint(),
            mode: default_echidna_mode(),
            timeout_secs: default_timeout(),
        }
    }
}

fn default_echidna_endpoint() -> String {
    "http://localhost:8080/graphql".to_string()
}

fn default_echidna_rest_endpoint() -> String {
    "http://localhost:8080".to_string()
}

fn default_echidna_mode() -> EchidnaApiMode {
    EchidnaApiMode::Auto
}

fn default_timeout() -> u64 {
    300 // 5 minutes
}

#[derive(Debug, Deserialize, Clone)]
pub struct GitHubConfig {
    /// GitHub App ID
    pub app_id: Option<u64>,

    /// Path to private key file
    pub private_key_path: Option<String>,

    /// Personal access token (alternative to app auth)
    pub token: Option<String>,

    /// Webhook secret for signature verification
    pub webhook_secret: Option<String>,
}

#[derive(Debug, Deserialize, Clone)]
pub struct GitLabConfig {
    /// GitLab instance URL
    pub url: String,

    /// Personal access token
    pub token: String,

    /// Webhook secret
    pub webhook_secret: Option<String>,
}

#[derive(Debug, Deserialize, Clone)]
pub struct SchedulerConfig {
    /// Maximum concurrent proof jobs
    #[serde(default = "default_max_concurrent")]
    pub max_concurrent: usize,

    /// Queue size limit
    #[serde(default = "default_queue_size")]
    pub queue_size: usize,
}

impl Default for SchedulerConfig {
    fn default() -> Self {
        Self {
            max_concurrent: default_max_concurrent(),
            queue_size: default_queue_size(),
        }
    }
}

fn default_max_concurrent() -> usize {
    5
}

fn default_queue_size() -> usize {
    100
}

impl Config {
    /// Load configuration from file
    pub fn load(path: &str) -> Result<Self> {
        let path = Path::new(path);

        if !path.exists() {
            tracing::warn!("Config file {} not found, using defaults", path.display());
            return Ok(Self::default());
        }

        let builder = config::Config::builder()
            .add_source(config::File::from(path))
            .add_source(config::Environment::with_prefix("ECHIDNABOT").separator("__"));

        let config = builder.build()?;
        let parsed: Config = config.try_deserialize()?;

        Ok(parsed)
    }
}

impl Default for Config {
    fn default() -> Self {
        Self {
            server: ServerConfig::default(),
            database: DatabaseConfig::default(),
            echidna: EchidnaConfig::default(),
            github: None,
            gitlab: None,
            scheduler: SchedulerConfig::default(),
        }
    }
}
