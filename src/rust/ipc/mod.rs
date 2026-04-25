// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! L1 IPC transport layer — Cap'n Proto over Unix domain sockets.
//!
//! Replaces the HTTP+JSON Rust↔Julia hot path used by `gnn/client.rs`.
//! Bindings generated from `schemas/echidna.capnp` via `just capnp-gen`.
//!
//! # Transport
//!
//! - **Primary**: Unix domain socket (UDS) at `$ECHIDNA_IPC_SOCK`
//!   (default: `/run/echidna/ipc.sock`)
//! - **Fallback**: TCP at `127.0.0.1:$ECHIDNA_IPC_PORT` (default: 9090)
//!
//! # Status
//!
//! Scaffolded (L1 wave 0). The schema (`schemas/echidna.capnp`) is complete.
//! Generated Rust bindings (`capnp compile -orust`) and the live transport
//! wiring are the L1 wave 1 deliverable, gated on L3 Tier-1 green for ≥ 7 days.
//!
//! Wire the Julia side in `src/julia/ipc.jl` in the same wave.

use anyhow::Result;
use std::path::PathBuf;
use tracing::info;

/// Default UDS socket path.
pub const DEFAULT_SOCK_PATH: &str = "/run/echidna/ipc.sock";
/// Default TCP fallback port.
pub const DEFAULT_TCP_PORT: u16 = 9090;

/// Transport selection for the IPC layer.
#[derive(Debug, Clone)]
pub enum Transport {
    /// Unix domain socket (primary — lowest latency, no network stack).
    Uds { path: PathBuf },
    /// TCP fallback — used when UDS is unavailable (e.g. cross-host).
    Tcp { host: String, port: u16 },
}

impl Default for Transport {
    fn default() -> Self {
        let path = std::env::var("ECHIDNA_IPC_SOCK")
            .map(PathBuf::from)
            .unwrap_or_else(|_| PathBuf::from(DEFAULT_SOCK_PATH));
        Transport::Uds { path }
    }
}

impl Transport {
    /// Build from environment variables.
    ///
    /// Checks `ECHIDNA_IPC_SOCK` (UDS) first; falls back to
    /// `ECHIDNA_IPC_HOST` + `ECHIDNA_IPC_PORT` (TCP).
    pub fn from_env() -> Self {
        if let Ok(sock) = std::env::var("ECHIDNA_IPC_SOCK") {
            return Transport::Uds { path: PathBuf::from(sock) };
        }
        // TCP only when ECHIDNA_IPC_HOST is explicitly set; otherwise UDS is primary.
        if let Ok(host) = std::env::var("ECHIDNA_IPC_HOST") {
            let port = std::env::var("ECHIDNA_IPC_PORT")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(DEFAULT_TCP_PORT);
            return Transport::Tcp { host, port };
        }
        Transport::Uds { path: PathBuf::from(DEFAULT_SOCK_PATH) }
    }

    /// Whether the transport endpoint appears reachable (best-effort probe).
    pub fn probe(&self) -> bool {
        match self {
            Transport::Uds { path } => path.exists(),
            Transport::Tcp { host, port } => {
                use std::net::TcpStream;
                use std::time::Duration;
                TcpStream::connect_timeout(
                    &format!("{}:{}", host, port).parse().unwrap_or_else(|_| {
                        "127.0.0.1:9090".parse().unwrap()
                    }),
                    Duration::from_millis(200),
                )
                .is_ok()
            },
        }
    }
}

/// IPC client stub.
///
/// Full implementation pending `capnp compile -orust schemas/echidna.capnp`
/// (L1 wave 1). Currently provides transport probing and config so that
/// callers can check availability and log the chosen transport before the
/// generated bindings land.
pub struct IpcClient {
    transport: Transport,
}

impl IpcClient {
    /// Create a client using the default transport (from env).
    pub fn new() -> Self {
        IpcClient { transport: Transport::from_env() }
    }

    /// Create a client with an explicit transport.
    pub fn with_transport(transport: Transport) -> Self {
        IpcClient { transport }
    }

    /// Whether the IPC server appears reachable.
    pub fn is_available(&self) -> bool {
        self.transport.probe()
    }

    /// Log transport configuration at INFO level.
    pub fn log_config(&self) {
        match &self.transport {
            Transport::Uds { path } => {
                info!("IPC transport: UDS at {:?} (available={})", path, self.is_available());
            },
            Transport::Tcp { host, port } => {
                info!("IPC transport: TCP {}:{} (available={})", host, port, self.is_available());
            },
        }
    }

    /// Placeholder: send a GNN rank request.
    ///
    /// Replaced by generated Cap'n Proto bindings in L1 wave 1.
    /// Returns `Err` so callers know to fall back to HTTP until the real
    /// implementation lands.
    pub async fn gnn_rank(&self, _request_json: &str) -> Result<String> {
        anyhow::bail!(
            "IPC GNN rank not yet implemented (L1 wave 1 pending). \
             Use HTTP fallback via gnn/client.rs."
        )
    }
}

impl Default for IpcClient {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_transport_from_env_defaults_to_uds() {
        std::env::remove_var("ECHIDNA_IPC_SOCK");
        std::env::remove_var("ECHIDNA_IPC_HOST");
        std::env::remove_var("ECHIDNA_IPC_PORT");
        let t = Transport::from_env();
        assert!(matches!(t, Transport::Uds { .. }));
    }

    #[test]
    fn test_transport_uds_probe_missing_sock() {
        let t = Transport::Uds { path: PathBuf::from("/tmp/echidna_no_such_sock_xyz.sock") };
        assert!(!t.probe());
    }

    #[test]
    fn test_ipc_client_gnn_rank_stub_errors() {
        let rt = tokio::runtime::Runtime::new().unwrap();
        let client = IpcClient::with_transport(Transport::Uds {
            path: PathBuf::from("/tmp/no_sock.sock"),
        });
        let result = rt.block_on(client.gnn_rank("{}"));
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("L1 wave 1 pending"));
    }
}
