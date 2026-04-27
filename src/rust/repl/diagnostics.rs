// SPDX-License-Identifier: PMPL-1.0-or-later
// Interactive diagnostics REPL for echidna

use std::io::{self, Write};

use echidna::diagnostics::{HealthStatus, DegradationMode};

/// Interactive diagnostics REPL
pub struct DiagnosticsREPL {
    prompt: String,
    history: Vec<String>,
}

impl DiagnosticsREPL {
    pub fn new() -> Self {
        DiagnosticsREPL {
            prompt: "echidna> ".to_string(),
            history: Vec::new(),
        }
    }

    /// Run interactive REPL loop
    pub async fn run(&mut self, health: &HealthStatus) {
        println!("\n=== ECHIDNA DIAGNOSTICS REPL ===");
        println!("Type 'help' for commands. 'exit' to quit.\n");

        loop {
            print!("{}", self.prompt);
            io::stdout().flush().unwrap();

            let mut input = String::new();
            match io::stdin().read_line(&mut input) {
                Ok(_) => {
                    let trimmed = input.trim();
                    if !trimmed.is_empty() {
                        self.history.push(trimmed.to_string());
                    }

                    match trimmed {
                        "exit" | "quit" => {
                            println!("Exiting diagnostics REPL.");
                            break;
                        }
                        "help" => self.print_help(),
                        "health" => self.print_health(health),
                        "summary" => println!("{}", health.summary()),
                        "degradation" => self.print_degradation(health),
                        "provers" => self.print_provers(health),
                        "critical" => self.print_critical(health),
                        "gnn" => self.print_gnn_status(health),
                        "corpus" => self.print_corpus_status(health),
                        "clear" => {
                            print!("\x1B[2J\x1B[1;1H");
                            io::stdout().flush().unwrap();
                        }
                        "history" => self.print_history(),
                        cmd => {
                            if cmd.starts_with("prover ") {
                                let name = cmd.strip_prefix("prover ").unwrap_or("");
                                self.print_prover_detail(health, name);
                            } else {
                                println!("Unknown command: '{}'. Type 'help' for available commands.", cmd);
                            }
                        }
                    }
                }
                Err(e) => {
                    eprintln!("Error reading input: {}", e);
                    break;
                }
            }
        }
    }

    fn print_help(&self) {
        println!("\nAvailable commands:");
        println!("  health                 - Show full health status");
        println!("  summary                - Show health summary");
        println!("  degradation            - Show current degradation mode");
        println!("  provers                - List all provers and their status");
        println!("  prover <name>          - Show details for a specific prover");
        println!("  critical               - Show provers in critical state");
        println!("  gnn                    - Show GNN model health");
        println!("  corpus                 - Show corpus health");
        println!("  history                - Show command history");
        println!("  clear                  - Clear screen");
        println!("  help                   - Show this help");
        println!("  exit / quit            - Exit REPL\n");
    }

    fn print_health(&self, health: &HealthStatus) {
        println!("\n=== ECHIDNA HEALTH STATUS ===");
        println!("Timestamp: {}", health.timestamp);
        println!("Overall Health: {:.1}%", health.health_percentage());
        println!("Degradation Mode: {:?}", health.system_degradation);
        println!("System Degraded: {}", if health.is_degraded() { "YES" } else { "NO" });
        println!("\nProvers: {} total", health.prover_health.len());

        let available = health
            .prover_health
            .values()
            .filter(|p| p.is_available)
            .count();
        println!("Available: {} ({:.1}%)", available,
            (available as f64 / health.prover_health.len().max(1) as f64) * 100.0);

        let failed = health
            .prover_health
            .values()
            .filter(|p| !p.is_available)
            .count();
        println!("Failed: {}", failed);

        println!("\nGNN Model:");
        println!("  Loaded: {}", if health.gnn_model_health.is_loaded { "YES" } else { "NO" });
        println!("  nDCG: {:.4}", health.gnn_model_health.last_validation_nDCG);
        println!("  MRR: {:.4}", health.gnn_model_health.last_validation_MRR);
        println!("  Meets threshold: {}", if health.gnn_model_health.nDCG_meets_threshold { "YES" } else { "NO" });
        println!("  Fallback active: {}", if health.gnn_model_health.fallback_active { "YES" } else { "NO" });
        println!("  Cache hit rate: {:.1}%", health.gnn_model_health.fallback_cache_hit_rate * 100.0);

        println!("\nCorpus:");
        println!("  Proofs: {}", health.corpus_health.total_proofs);
        println!("  Premises: {}", health.corpus_health.total_premises);
        println!("  Size: {:.1} MB", health.corpus_health.size_mb);
        if let Some(updated) = health.corpus_health.last_updated {
            println!("  Last updated: {}", updated);
        }
        println!();
    }

    fn print_degradation(&self, health: &HealthStatus) {
        println!("\n=== DEGRADATION MODE ===");
        println!("Current mode: {:?}\n", health.system_degradation);

        match health.system_degradation {
            DegradationMode::Normal => {
                println!("System is operating normally.");
                println!("All prover backends and GNN ranking are available.");
            }
            DegradationMode::IncreasingFallback => {
                println!("System is partially degraded.");
                println!("Increasing use of cosine similarity fallback (~30% of queries).");
                println!("Limiting prover portfolio to top 5 best performers.");
            }
            DegradationMode::CosineOnly => {
                println!("System is severely degraded.");
                println!("All queries routed to cosine similarity fallback.");
                println!("GNN model is unavailable or not meeting quality threshold.");
                println!("Recommend: restart GNN service, check model weights, retrain if needed.");
            }
            DegradationMode::ReadOnly => {
                println!("System is in read-only mode.");
                println!("No new proof search. Pre-submitted proofs only.");
                println!("GNN training disabled. All operations fallback-only.");
                println!("Recommend: immediate investigation and service restart.");
            }
            DegradationMode::Minimal => {
                println!("System is in minimal mode (critical).");
                println!("Only pre-submitted proofs accepted.");
                println!("No new proof attempts. No training. Emergency-only operation.");
                println!("ALERT: Service may need maintenance or restart.");
            }
        }
        println!();
    }

    fn print_provers(&self, health: &HealthStatus) {
        println!("\n=== PROVER STATUS ===\n");
        println!(
            "{:<20} {:<12} {:<15} {:<10} {:<10}",
            "Name", "Available", "Circuit State", "Latency", "Success%"
        );
        println!("{}", "-".repeat(70));

        let mut provers: Vec<_> = health.prover_health.values().collect();
        provers.sort_by_key(|p| &p.name);

        for prover in provers {
            let state = format!("{:?}", prover.circuit_breaker_state);
            let available = if prover.is_available { "YES" } else { "NO" };
            let success_pct = prover.success_rate * 100.0;
            println!(
                "{:<20} {:<12} {:<15} {:<10.1} {:<10.1}%",
                prover.name, available, state, prover.avg_latency_ms, success_pct
            );
        }
        println!();
    }

    fn print_prover_detail(&self, health: &HealthStatus, name: &str) {
        match health.prover_health.get(name) {
            Some(prover) => {
                println!("\n=== PROVER: {} ===", prover.name);
                println!("Available: {}", if prover.is_available { "YES" } else { "NO" });
                println!("Circuit state: {:?}", prover.circuit_breaker_state);
                println!("Consecutive failures: {}", prover.consecutive_failures);
                println!("Avg latency: {:.2} ms", prover.avg_latency_ms);
                println!("Success rate: {:.2}%", prover.success_rate * 100.0);
                println!("Total invocations: {}", prover.total_invocations);
                println!("Total failures: {}", prover.total_failures);
                if let Some(last_success) = prover.last_successful_proof {
                    println!("Last successful proof: {}", last_success);
                } else {
                    println!("Last successful proof: never");
                }
                println!();
            }
            None => {
                println!("Prover '{}' not found.", name);
            }
        }
    }

    fn print_critical(&self, health: &HealthStatus) {
        let critical = health.critical_provers();
        if critical.is_empty() {
            println!("\n✓ No critical provers (all circuit breakers closed)\n");
        } else {
            println!("\n⚠️ CRITICAL PROVERS (circuit breakers open):\n");
            for name in critical {
                println!("  - {}", name);
            }
            println!();
        }
    }

    fn print_gnn_status(&self, health: &HealthStatus) {
        println!("\n=== GNN MODEL STATUS ===");
        println!("Loaded: {}", if health.gnn_model_health.is_loaded { "YES" } else { "NO" });

        if let Some(checksum) = &health.gnn_model_health.model_checksum {
            println!("Checksum: {}", checksum);
        }

        if let Some(trained) = health.gnn_model_health.last_trained {
            println!("Last trained: {}", trained);
        }

        println!("Validation metrics:");
        println!("  nDCG: {:.4}", health.gnn_model_health.last_validation_nDCG);
        println!("  MRR: {:.4}", health.gnn_model_health.last_validation_MRR);
        println!("  Meets threshold (nDCG ≥ 0.60): {}",
            if health.gnn_model_health.nDCG_meets_threshold { "YES" } else { "NO" });

        println!("\nFallback (cosine similarity):");
        println!("  Active: {}", if health.gnn_model_health.fallback_active { "YES" } else { "NO" });
        println!("  Cache size: {} goals", health.gnn_model_health.fallback_cache_size);
        println!("  Cache hit rate: {:.1}%", health.gnn_model_health.fallback_cache_hit_rate * 100.0);
        println!("  Max latency: {:.1} ms", health.gnn_model_health.fallback_max_latency_ms);
        println!();
    }

    fn print_corpus_status(&self, health: &HealthStatus) {
        println!("\n=== CORPUS STATUS ===");
        println!("Total proofs: {}", health.corpus_health.total_proofs);
        println!("Total premises: {}", health.corpus_health.total_premises);
        println!("Size: {:.1} MB", health.corpus_health.size_mb);
        println!("Size change: {:.1}%", health.corpus_health.size_change_percent);

        if let Some(updated) = health.corpus_health.last_updated {
            println!("Last updated: {}", updated);
        }
        println!();
    }

    fn print_history(&self) {
        println!("\n=== COMMAND HISTORY ===");
        for (i, cmd) in self.history.iter().enumerate() {
            println!("{:3}: {}", i + 1, cmd);
        }
        println!();
    }
}

impl Default for DiagnosticsREPL {
    fn default() -> Self {
        Self::new()
    }
}
