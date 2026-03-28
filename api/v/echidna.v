// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// ECHIDNA V-lang API — Multi-backend theorem prover client.
module echidna

pub enum ProverBackend {
	coq
	lean4
	idris2
	z3
	hol4
	hol_light
	isabelle
	mizar
	metamath
	pvs
	agda
	acl2
}

pub enum ProofStatus {
	proven
	disproven
	timeout
	@error
	unknown
}

pub struct ProofRequest {
pub:
	goal       string
	hypotheses []string
	backend    ProverBackend
	timeout_ms int
}

pub struct ProofResult {
pub:
	status     ProofStatus
	proof_text string
	backend    ProverBackend
	time_ms    int
}

fn C.echidna_prove(goal_ptr &u8, backend int, timeout_ms int) int
fn C.echidna_valid_backend(backend int) int
fn C.echidna_backend_count() int

// prove submits a proof goal to the specified backend.
pub fn prove(req ProofRequest) ProofResult {
	result := C.echidna_prove(req.goal.str, int(req.backend), req.timeout_ms)
	return ProofResult{
		status: unsafe { ProofStatus(result) }
		proof_text: ''
		backend: req.backend
		time_ms: 0
	}
}

// is_valid_backend checks if a backend ID is supported.
pub fn is_valid_backend(backend ProverBackend) bool {
	return C.echidna_valid_backend(int(backend)) == 1
}

// backend_count returns the number of supported prover backends.
pub fn backend_count() int {
	return C.echidna_backend_count()
}
