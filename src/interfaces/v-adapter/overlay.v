// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// ECHIDNA Overlay Network REST API Gateway
//
// Exposes Tor, IPFS, and Ethereum overlay network operations via REST on port 8103:
//
//   Unified:
//     GET  /api/v1/overlay/health             — overlay subsystem health
//     GET  /api/v1/overlay/status             — combined status of all networks
//     GET  /api/v1/overlay/version            — overlay module version
//
//   Tor:
//     POST /api/v1/overlay/tor/connect        — connect to Tor control port
//     POST /api/v1/overlay/tor/disconnect     — disconnect from Tor
//     GET  /api/v1/overlay/tor/status         — Tor connection status
//     POST /api/v1/overlay/tor/hidden-service — create hidden service
//     DELETE /api/v1/overlay/tor/hidden-service/:onion — destroy hidden service
//     GET  /api/v1/overlay/tor/circuits       — list active circuits
//     GET  /api/v1/overlay/tor/circuits/:id   — get circuit details
//     POST /api/v1/overlay/tor/resolve        — resolve hostname through Tor
//
//   IPFS:
//     POST /api/v1/overlay/ipfs/connect       — connect to IPFS daemon
//     POST /api/v1/overlay/ipfs/disconnect    — disconnect from IPFS
//     GET  /api/v1/overlay/ipfs/status        — IPFS connection status
//     POST /api/v1/overlay/ipfs/add           — add content, returns CID
//     GET  /api/v1/overlay/ipfs/cat/:cid      — retrieve content by CID
//     POST /api/v1/overlay/ipfs/pin           — pin content by CID
//     POST /api/v1/overlay/ipfs/unpin         — unpin content by CID
//     GET  /api/v1/overlay/ipfs/dag/:cid      — get DAG node
//
//   Ethereum (stubbed — Aerie future use):
//     POST /api/v1/overlay/eth/connect        — connect to Ethereum RPC
//     POST /api/v1/overlay/eth/disconnect     — disconnect from Ethereum
//     GET  /api/v1/overlay/eth/status         — Ethereum connection status
//     POST /api/v1/overlay/eth/timestamp-proof — anchor proof hash on-chain
//     POST /api/v1/overlay/eth/verify-timestamp — verify anchored timestamp
//
// Links against libechidna_overlay.so (Zig FFI layer) when available.
// Falls back to stub responses with X-Overlay-Mode: stub header when FFI is absent.

module main

import net.http
import time

// --- Zig FFI extern declarations (libechidna_overlay.so) ---

#flag -L @VMODROOT/../../ffi/zig/zig-out/lib
#flag -lechidna_overlay

// Tor
fn C.echidna_tor_connect(config_ptr &u8, config_len usize) int
fn C.echidna_tor_disconnect()
fn C.echidna_tor_create_hidden_service(port int, target_port int, out_ptr &u8, out_len &usize) int
fn C.echidna_tor_destroy_hidden_service(onion_ptr &u8, onion_len usize) int
fn C.echidna_tor_get_circuit(circuit_id int, out_ptr &u8, out_len &usize) int
fn C.echidna_tor_list_circuits(out_ptr &u8, out_len &usize) int
fn C.echidna_tor_resolve(hostname_ptr &u8, hostname_len usize, out_ptr &u8, out_len &usize) int
fn C.echidna_tor_status() int
fn C.echidna_tor_hidden_service_count() int

// IPFS
fn C.echidna_ipfs_connect(config_ptr &u8, config_len usize) int
fn C.echidna_ipfs_disconnect()
fn C.echidna_ipfs_add(data_ptr &u8, data_len usize, out_cid_ptr &u8, out_cid_len &usize) int
fn C.echidna_ipfs_cat(cid_ptr &u8, cid_len usize, out_ptr &u8, out_len &usize) int
fn C.echidna_ipfs_pin(cid_ptr &u8, cid_len usize) int
fn C.echidna_ipfs_unpin(cid_ptr &u8, cid_len usize) int
fn C.echidna_ipfs_dag_get(cid_ptr &u8, cid_len usize, out_ptr &u8, out_len &usize) int
fn C.echidna_ipfs_status() int
fn C.echidna_ipfs_pin_count() int

// Ethereum (stubbed)
fn C.echidna_eth_connect(config_ptr &u8, config_len usize) int
fn C.echidna_eth_disconnect()
fn C.echidna_eth_timestamp_proof(proof_hash_ptr &u8, proof_hash_len usize, out_ptr &u8, out_len &usize) int
fn C.echidna_eth_verify_timestamp(tx_hash_ptr &u8, tx_hash_len usize, out_ptr &u8, out_len &usize) int
fn C.echidna_eth_status() int

// Unified
fn C.echidna_overlay_version() &u8
fn C.echidna_overlay_kind_name(kind int) &u8
fn C.echidna_overlay_last_error() &u8

// Callback registration (Zig FFI bidirectional callbacks)
// Signatures must match Zig OnStatusChangeFn, OnErrorFn, OnProgressFn, OnCircuitChangeFn, OnPinChangeFn
fn C.echidna_overlay_register_on_status_change(cb fn (int, int, int) ) int
fn C.echidna_overlay_register_on_error(cb fn (int, int, &u8, usize) ) int
fn C.echidna_overlay_register_on_progress(cb fn (int, int, u64, u64) ) int
fn C.echidna_overlay_register_on_circuit_change(cb fn (int, int, int) ) int
fn C.echidna_overlay_register_on_pin_change(cb fn (&u8, usize, int, int) ) int
fn C.echidna_overlay_unregister_all_callbacks() int
fn C.echidna_overlay_callback_count() int

// --- Overlay Event Buffer ---

struct OverlayEvent {
	kind      string
	timestamp string
	data      string
}

__global overlay_event_buffer = []OverlayEvent{}
__global overlay_event_buffer_max = 1000

fn push_overlay_event(kind string, data string) {
	if overlay_event_buffer.len >= overlay_event_buffer_max {
		overlay_event_buffer.delete(0)
	}
	overlay_event_buffer << OverlayEvent{
		kind: kind
		timestamp: time.now().format_rfc3339()
		data: data
	}
}

fn on_overlay_status_callback(kind int, old_status int, new_status int) {
	kind_name := match kind {
		0 { 'tor' }
		1 { 'ipfs' }
		2 { 'ethereum' }
		else { 'unknown' }
	}
	push_overlay_event('status', '{"kind":"${kind_name}","old_status":${old_status},"new_status":${new_status},"new_name":"${status_name(new_status)}"}')
}

fn on_overlay_error_callback(kind int, error_code int, msg_ptr &u8, msg_len usize) {
	msg := if msg_ptr != unsafe { nil } && msg_len > 0 {
		unsafe { tos(msg_ptr, int(msg_len)) }
	} else {
		'unknown error'
	}
	push_overlay_event('error', '{"kind":${kind},"error_code":${error_code},"message":"${esc(msg)}"}')
}

fn on_overlay_progress_callback(kind int, operation_id int, bytes_done u64, bytes_total u64) {
	push_overlay_event('progress', '{"kind":${kind},"operation_id":${operation_id},"bytes_done":${bytes_done},"bytes_total":${bytes_total}}')
}

fn on_overlay_circuit_callback(circuit_id int, old_status int, new_status int) {
	push_overlay_event('circuit', '{"circuit_id":${circuit_id},"old_status":${old_status},"new_status":${new_status}}')
}

fn on_overlay_pin_callback(cid_ptr &u8, cid_len usize, old_status int, new_status int) {
	cid := if cid_ptr != unsafe { nil } && cid_len > 0 {
		unsafe { tos(cid_ptr, int(cid_len)) }
	} else {
		'unknown'
	}
	push_overlay_event('pin', '{"cid":"${esc(cid)}","old_status":${old_status},"new_status":${new_status}}')
}

// Track whether FFI is available (set during init)
__global overlay_ffi_available = false
__global overlay_ffi_initialised = false

fn init_overlay_ffi() {
	// Test connectivity by reading version — if we can call it, the library is linked
	ptr := C.echidna_overlay_version()
	if ptr != unsafe { nil } {
		ver := unsafe { cstring_to_vstring(ptr) }
		if ver.len > 0 {
			overlay_ffi_available = true
			overlay_ffi_initialised = true
			// Register bidirectional callbacks (signatures match Zig OnStatusChangeFn etc.)
			C.echidna_overlay_register_on_status_change(on_overlay_status_callback)
			C.echidna_overlay_register_on_error(on_overlay_error_callback)
			C.echidna_overlay_register_on_progress(on_overlay_progress_callback)
			C.echidna_overlay_register_on_circuit_change(on_overlay_circuit_callback)
			C.echidna_overlay_register_on_pin_change(on_overlay_pin_callback)
			println('  FFI: linked to libechidna_overlay.so v${ver} (live mode, ${C.echidna_overlay_callback_count()} callbacks registered)')
			return
		}
	}
	overlay_ffi_available = false
	println('  FFI: overlay library not available (stub mode)')
}

fn overlay_response(status_code int, body string) http.Response {
	mut header := http.new_header(key: .content_type, value: 'application/json')
	if !overlay_ffi_available {
		header.add_custom('X-Overlay-Mode', 'stub') or {}
	} else {
		header.add_custom('X-Overlay-Mode', 'live') or {}
	}
	return http.new_response(
		status: unsafe { http.Status(status_code) }
		header: header
		body: body
	)
}

fn overlay_last_error() string {
	ptr := C.echidna_overlay_last_error()
	if ptr == unsafe { nil } {
		return 'unknown error'
	}
	return unsafe { cstring_to_vstring(ptr) }
}

fn overlay_version() string {
	ptr := C.echidna_overlay_version()
	return unsafe { cstring_to_vstring(ptr) }
}

fn status_name(code int) string {
	return match code {
		0 { 'disconnected' }
		1 { 'connecting' }
		2 { 'connected' }
		3 { 'error' }
		else { 'unknown' }
	}
}

// --- Handler ---

struct OverlayHandler {
	port int
}

pub fn (mut h OverlayHandler) handle(req http.Request) http.Response {
	path := req.url.all_before('?')
	prefix := '/api/v1/overlay'

	// Route: GET / — API discovery
	if path == '/' && req.method == .get {
		return handle_overlay_info()
	}

	// === Unified ===
	if path == '${prefix}/events' && req.method == .get {
		return handle_overlay_events()
	}
	if path == '${prefix}/health' && req.method == .get {
		return handle_overlay_health()
	}
	if path == '${prefix}/status' && req.method == .get {
		return handle_overlay_status()
	}
	if path == '${prefix}/version' && req.method == .get {
		return handle_overlay_version()
	}

	// === Tor ===
	if path == '${prefix}/tor/connect' && req.method == .post {
		return handle_tor_connect(req)
	}
	if path == '${prefix}/tor/disconnect' && req.method == .post {
		return handle_tor_disconnect()
	}
	if path == '${prefix}/tor/status' && req.method == .get {
		return handle_tor_status()
	}
	if path == '${prefix}/tor/hidden-service' && req.method == .post {
		return handle_tor_create_hidden_service(req)
	}
	if path.starts_with('${prefix}/tor/hidden-service/') && req.method == .delete {
		onion := path.all_after('${prefix}/tor/hidden-service/')
		return handle_tor_destroy_hidden_service(onion)
	}
	if path == '${prefix}/tor/circuits' && req.method == .get {
		return handle_tor_list_circuits()
	}
	if path.starts_with('${prefix}/tor/circuits/') && req.method == .get {
		circuit_id := path.all_after('${prefix}/tor/circuits/')
		return handle_tor_get_circuit(circuit_id)
	}
	if path == '${prefix}/tor/resolve' && req.method == .post {
		return handle_tor_resolve(req)
	}

	// === IPFS ===
	if path == '${prefix}/ipfs/connect' && req.method == .post {
		return handle_ipfs_connect(req)
	}
	if path == '${prefix}/ipfs/disconnect' && req.method == .post {
		return handle_ipfs_disconnect()
	}
	if path == '${prefix}/ipfs/status' && req.method == .get {
		return handle_ipfs_status()
	}
	if path == '${prefix}/ipfs/add' && req.method == .post {
		return handle_ipfs_add(req)
	}
	if path.starts_with('${prefix}/ipfs/cat/') && req.method == .get {
		cid := path.all_after('${prefix}/ipfs/cat/')
		return handle_ipfs_cat(cid)
	}
	if path == '${prefix}/ipfs/pin' && req.method == .post {
		return handle_ipfs_pin(req)
	}
	if path == '${prefix}/ipfs/unpin' && req.method == .post {
		return handle_ipfs_unpin(req)
	}
	if path.starts_with('${prefix}/ipfs/dag/') && req.method == .get {
		cid := path.all_after('${prefix}/ipfs/dag/')
		return handle_ipfs_dag_get(cid)
	}

	// === Ethereum ===
	if path == '${prefix}/eth/connect' && req.method == .post {
		return handle_eth_connect(req)
	}
	if path == '${prefix}/eth/disconnect' && req.method == .post {
		return handle_eth_disconnect()
	}
	if path == '${prefix}/eth/status' && req.method == .get {
		return handle_eth_status()
	}
	if path == '${prefix}/eth/timestamp-proof' && req.method == .post {
		return handle_eth_timestamp_proof(req)
	}
	if path == '${prefix}/eth/verify-timestamp' && req.method == .post {
		return handle_eth_verify_timestamp(req)
	}

	return overlay_response(404, '{"error":"Not found","service":"echidna-overlay","endpoints":["/api/v1/overlay/health","/api/v1/overlay/status","/api/v1/overlay/tor/*","/api/v1/overlay/ipfs/*","/api/v1/overlay/eth/*"]}')
}

// --- Server ---

pub struct OverlayServer {
pub mut:
	port int
}

pub fn new_overlay_server(port int) &OverlayServer {
	return &OverlayServer{
		port: port
	}
}

pub fn (s OverlayServer) start() {
	println('ECHIDNA Overlay REST API Gateway starting on port ${s.port}...')
	init_overlay_ffi()
	println('  === Unified ===')
	println('  GET  /api/v1/overlay/health                      — subsystem health')
	println('  GET  /api/v1/overlay/status                      — combined status')
	println('  GET  /api/v1/overlay/version                     — overlay version')
	println('  === Tor ===')
	println('  POST /api/v1/overlay/tor/connect                 — connect to Tor')
	println('  POST /api/v1/overlay/tor/disconnect              — disconnect from Tor')
	println('  GET  /api/v1/overlay/tor/status                  — connection status')
	println('  POST /api/v1/overlay/tor/hidden-service          — create hidden service')
	println('  DELETE /api/v1/overlay/tor/hidden-service/:onion — destroy hidden service')
	println('  GET  /api/v1/overlay/tor/circuits                — list circuits')
	println('  GET  /api/v1/overlay/tor/circuits/:id            — circuit details')
	println('  POST /api/v1/overlay/tor/resolve                 — resolve via Tor')
	println('  === IPFS ===')
	println('  POST /api/v1/overlay/ipfs/connect                — connect to IPFS')
	println('  POST /api/v1/overlay/ipfs/disconnect             — disconnect from IPFS')
	println('  GET  /api/v1/overlay/ipfs/status                 — connection status')
	println('  POST /api/v1/overlay/ipfs/add                    — add content')
	println('  GET  /api/v1/overlay/ipfs/cat/:cid               — retrieve by CID')
	println('  POST /api/v1/overlay/ipfs/pin                    — pin content')
	println('  POST /api/v1/overlay/ipfs/unpin                  — unpin content')
	println('  GET  /api/v1/overlay/ipfs/dag/:cid               — DAG node')
	println('  === Ethereum (stubbed) ===')
	println('  POST /api/v1/overlay/eth/connect                 — connect to Ethereum')
	println('  POST /api/v1/overlay/eth/disconnect              — disconnect')
	println('  GET  /api/v1/overlay/eth/status                  — connection status')
	println('  POST /api/v1/overlay/eth/timestamp-proof         — anchor proof on-chain')
	println('  POST /api/v1/overlay/eth/verify-timestamp        — verify timestamp')
	mut server := http.Server{
		addr: ':${s.port}'
		handler: &OverlayHandler{port: s.port}
	}
	server.listen_and_serve()
}

fn main() {
	mut s := new_overlay_server(8103)
	s.start()
}

// ============================================================================
// Unified Handlers
// ============================================================================

fn handle_overlay_info() http.Response {
	if overlay_ffi_available {
		ver := overlay_version()
		return overlay_response(200, '{"service":"echidna-overlay","version":"${ver}","description":"ECHIDNA overlay network gateway (Tor, IPFS, Ethereum)","networks":["tor","ipfs","ethereum"],"endpoints":["/api/v1/overlay/health","/api/v1/overlay/status","/api/v1/overlay/tor/*","/api/v1/overlay/ipfs/*","/api/v1/overlay/eth/*"],"documentation":"https://github.com/hyperpolymath/echidna"}')
	}
	return overlay_response(200, '{"service":"echidna-overlay","version":"1.0.0","description":"ECHIDNA overlay network gateway (Tor, IPFS, Ethereum)","networks":["tor","ipfs","ethereum"],"endpoints":["/api/v1/overlay/health","/api/v1/overlay/status","/api/v1/overlay/tor/*","/api/v1/overlay/ipfs/*","/api/v1/overlay/eth/*"],"documentation":"https://github.com/hyperpolymath/echidna"}')
}

fn handle_overlay_events() http.Response {
	if overlay_event_buffer.len == 0 {
		return overlay_response(200, '{"events":[],"count":0,"message":"No pending overlay events"}')
	}
	mut items := []string{}
	for ev in overlay_event_buffer {
		items << '{"kind":"${esc(ev.kind)}","timestamp":"${esc(ev.timestamp)}","data":${ev.data}}'
	}
	count := overlay_event_buffer.len
	overlay_event_buffer.clear()
	return overlay_response(200, '{"events":[${items.join(",")}],"count":${count}}')
}

fn handle_overlay_health() http.Response {
	now := time.now()
	if overlay_ffi_available {
		ver := overlay_version()
		tor := status_name(C.echidna_tor_status())
		ipfs := status_name(C.echidna_ipfs_status())
		eth := status_name(C.echidna_eth_status())
		return overlay_response(200, '{"healthy":true,"service":"echidna-overlay","version":"${ver}","tor":"${tor}","ipfs":"${ipfs}","ethereum":"${eth}","uptime_seconds":${now.unix()},"ffi_mode":"live"}')
	}
	return overlay_response(200, '{"healthy":true,"service":"echidna-overlay","version":"1.0.0","tor":"disconnected","ipfs":"disconnected","ethereum":"disconnected","uptime_seconds":${now.unix()},"ffi_mode":"stub"}')
}

fn handle_overlay_status() http.Response {
	if overlay_ffi_available {
		tor := status_name(C.echidna_tor_status())
		ipfs := status_name(C.echidna_ipfs_status())
		eth := status_name(C.echidna_eth_status())
		tor_hs := C.echidna_tor_hidden_service_count()
		ipfs_pins := C.echidna_ipfs_pin_count()
		return overlay_response(200, '{"tor":{"status":"${tor}","hidden_services":${tor_hs}},"ipfs":{"status":"${ipfs}","pinned_items":${ipfs_pins}},"ethereum":{"status":"${eth}","note":"Stubbed — awaiting Aerie integration"}}')
	}
	return overlay_response(200, '{"tor":{"status":"disconnected","hidden_services":0},"ipfs":{"status":"disconnected","pinned_items":0},"ethereum":{"status":"disconnected","note":"Stubbed — awaiting Aerie integration"}}')
}

fn handle_overlay_version() http.Response {
	if overlay_ffi_available {
		ver := overlay_version()
		return overlay_response(200, '{"version":"${ver}"}')
	}
	return overlay_response(200, '{"version":"1.0.0"}')
}

// ============================================================================
// Tor Handlers
// ============================================================================

fn handle_tor_connect(req http.Request) http.Response {
	config := if req.data.len > 0 { req.data } else { '{"control_port":9051}' }
	if overlay_ffi_available {
		rc := C.echidna_tor_connect(config.str, usize(config.len))
		if rc == 0 {
			return overlay_response(200, '{"connected":true,"network":"tor","control_port":9051,"socks_port":9050,"message":"Connected to Tor control port"}')
		}
		err := overlay_last_error()
		return overlay_response(500, '{"connected":false,"network":"tor","error":"${esc(err)}"}')
	}
	return overlay_response(200, '{"connected":true,"network":"tor","control_port":9051,"socks_port":9050,"message":"Connected to Tor control port (stub)"}')
}

fn handle_tor_disconnect() http.Response {
	if overlay_ffi_available {
		C.echidna_tor_disconnect()
	}
	return overlay_response(200, '{"disconnected":true,"network":"tor","message":"Disconnected from Tor"}')
}

fn handle_tor_status() http.Response {
	if overlay_ffi_available {
		status := status_name(C.echidna_tor_status())
		hs_count := C.echidna_tor_hidden_service_count()
		return overlay_response(200, '{"network":"tor","status":"${status}","hidden_services":${hs_count}}')
	}
	return overlay_response(200, '{"network":"tor","status":"disconnected","hidden_services":0}')
}

fn handle_tor_create_hidden_service(req http.Request) http.Response {
	if req.data.len == 0 {
		return overlay_response(400, '{"error":"Request body required with port and target_port fields"}')
	}
	port := json_field_int(req.data, 'port')
	target_port := json_field_int(req.data, 'target_port')
	if port <= 0 || target_port <= 0 {
		return overlay_response(400, '{"error":"Both port and target_port must be positive integers"}')
	}
	if overlay_ffi_available {
		mut buf := [128]u8{}
		mut buf_len := usize(128)
		rc := C.echidna_tor_create_hidden_service(port, target_port, &buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			onion := unsafe { tos(&buf[0], int(buf_len)) }
			hs_count := C.echidna_tor_hidden_service_count()
			return overlay_response(201, '{"created":true,"onion_address":"${esc(onion)}","port":${port},"target_port":${target_port},"active_services":${hs_count},"created_at":"${time.now().format_rfc3339()}"}')
		}
		err := overlay_last_error()
		return overlay_response(500, '{"created":false,"error":"${esc(err)}","port":${port},"target_port":${target_port}}')
	}
	return overlay_response(201, '{"created":true,"onion_address":"echidna2fproof7verify3trust8secure4formal5check6valid.onion","port":${port},"target_port":${target_port},"active_services":1,"created_at":"${time.now().format_rfc3339()}"}')
}

fn handle_tor_destroy_hidden_service(onion string) http.Response {
	if onion.len == 0 {
		return overlay_response(400, '{"error":"Onion address required in URL path"}')
	}
	if overlay_ffi_available {
		rc := C.echidna_tor_destroy_hidden_service(onion.str, usize(onion.len))
		if rc == 0 {
			hs_count := C.echidna_tor_hidden_service_count()
			return overlay_response(200, '{"destroyed":true,"onion_address":"${esc(onion)}","remaining_services":${hs_count}}')
		}
		err := overlay_last_error()
		return overlay_response(500, '{"destroyed":false,"onion_address":"${esc(onion)}","error":"${esc(err)}"}')
	}
	return overlay_response(200, '{"destroyed":true,"onion_address":"${esc(onion)}","remaining_services":0}')
}

fn handle_tor_list_circuits() http.Response {
	if overlay_ffi_available {
		mut buf := [8192]u8{}
		mut buf_len := usize(8192)
		rc := C.echidna_tor_list_circuits(&buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			circuits := unsafe { tos(&buf[0], int(buf_len)) }
			return overlay_response(200, '{"network":"tor","circuits":${circuits}}')
		}
		err := overlay_last_error()
		return overlay_response(500, '{"network":"tor","error":"${esc(err)}"}')
	}
	return overlay_response(200, '{"network":"tor","circuits":[{"circuit_id":1,"status":"BUILT","hop_count":3,"purpose":"GENERAL"}]}')
}

fn handle_tor_get_circuit(circuit_id_str string) http.Response {
	circuit_id := circuit_id_str.int()
	if overlay_ffi_available {
		mut buf := [8192]u8{}
		mut buf_len := usize(8192)
		rc := C.echidna_tor_get_circuit(circuit_id, &buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			circuit := unsafe { tos(&buf[0], int(buf_len)) }
			return overlay_response(200, circuit)
		}
		err := overlay_last_error()
		return overlay_response(500, '{"network":"tor","circuit_id":${circuit_id},"error":"${esc(err)}"}')
	}
	return overlay_response(200, '{"circuit_id":${circuit_id},"status":"BUILT","path":[{"fingerprint":"AAAA...","nickname":"Guard1","country":"DE","is_exit":false},{"fingerprint":"BBBB...","nickname":"Middle1","country":"NL","is_exit":false},{"fingerprint":"CCCC...","nickname":"Exit1","country":"SE","is_exit":true}],"purpose":"GENERAL","time_created":"${time.now().format_rfc3339()}"}')
}

fn handle_tor_resolve(req http.Request) http.Response {
	if req.data.len == 0 {
		return overlay_response(400, '{"error":"Request body required with hostname field"}')
	}
	hostname := json_field(req.data, 'hostname')
	if hostname.len == 0 {
		return overlay_response(400, '{"error":"hostname field required"}')
	}
	if overlay_ffi_available {
		mut buf := [256]u8{}
		mut buf_len := usize(256)
		rc := C.echidna_tor_resolve(hostname.str, usize(hostname.len), &buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			resolved := unsafe { tos(&buf[0], int(buf_len)) }
			return overlay_response(200, '{"hostname":"${esc(hostname)}","resolved":"${esc(resolved)}","via":"tor-socks5"}')
		}
		err := overlay_last_error()
		return overlay_response(500, '{"hostname":"${esc(hostname)}","error":"${esc(err)}"}')
	}
	return overlay_response(200, '{"hostname":"${esc(hostname)}","resolved":"198.51.100.42","via":"tor-socks5"}')
}

// ============================================================================
// IPFS Handlers
// ============================================================================

fn handle_ipfs_connect(req http.Request) http.Response {
	config := if req.data.len > 0 { req.data } else { '{"api_port":5001}' }
	if overlay_ffi_available {
		rc := C.echidna_ipfs_connect(config.str, usize(config.len))
		if rc == 0 {
			return overlay_response(200, '{"connected":true,"network":"ipfs","api_port":5001,"gateway_port":8080,"message":"Connected to IPFS daemon"}')
		}
		err := overlay_last_error()
		return overlay_response(500, '{"connected":false,"network":"ipfs","error":"${esc(err)}"}')
	}
	return overlay_response(200, '{"connected":true,"network":"ipfs","api_port":5001,"gateway_port":8080,"message":"Connected to IPFS daemon (stub)"}')
}

fn handle_ipfs_disconnect() http.Response {
	if overlay_ffi_available {
		C.echidna_ipfs_disconnect()
	}
	return overlay_response(200, '{"disconnected":true,"network":"ipfs","message":"Disconnected from IPFS"}')
}

fn handle_ipfs_status() http.Response {
	if overlay_ffi_available {
		status := status_name(C.echidna_ipfs_status())
		pin_count := C.echidna_ipfs_pin_count()
		return overlay_response(200, '{"network":"ipfs","status":"${status}","pinned_items":${pin_count}}')
	}
	return overlay_response(200, '{"network":"ipfs","status":"disconnected","pinned_items":0}')
}

fn handle_ipfs_add(req http.Request) http.Response {
	if req.data.len == 0 {
		return overlay_response(400, '{"error":"Request body required with data field"}')
	}
	data := json_field(req.data, 'data')
	if data.len == 0 {
		return overlay_response(400, '{"error":"data field required"}')
	}
	content_type := json_field_or(req.data, 'content_type', 'application/octet-stream')
	if overlay_ffi_available {
		mut cid_buf := [256]u8{}
		mut cid_len := usize(256)
		rc := C.echidna_ipfs_add(data.str, usize(data.len), &cid_buf[0], &cid_len)
		if rc == 0 && cid_len > 0 {
			cid := unsafe { tos(&cid_buf[0], int(cid_len)) }
			return overlay_response(201, '{"added":true,"cid":"${esc(cid)}","size":${data.len},"content_type":"${esc(content_type)}","added_at":"${time.now().format_rfc3339()}"}')
		}
		err := overlay_last_error()
		return overlay_response(500, '{"added":false,"error":"${esc(err)}"}')
	}
	return overlay_response(201, '{"added":true,"cid":"bafkreihdwdcefgh4dqkjv67uzcmw7ojee6xedzdetojuzjevtenrqpc","size":${data.len},"content_type":"${esc(content_type)}","added_at":"${time.now().format_rfc3339()}"}')
}

fn handle_ipfs_cat(cid string) http.Response {
	if cid.len == 0 {
		return overlay_response(400, '{"error":"CID required in URL path"}')
	}
	if overlay_ffi_available {
		mut buf := [65536]u8{}
		mut buf_len := usize(65536)
		rc := C.echidna_ipfs_cat(cid.str, usize(cid.len), &buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			content := unsafe { tos(&buf[0], int(buf_len)) }
			return overlay_response(200, '{"cid":"${esc(cid)}","content":"${esc(content)}","size":${buf_len}}')
		}
		err := overlay_last_error()
		return overlay_response(500, '{"cid":"${esc(cid)}","error":"${esc(err)}"}')
	}
	return overlay_response(200, '{"cid":"${esc(cid)}","content":"(* ECHIDNA proof certificate — retrieved from IPFS *)","size":54}')
}

fn handle_ipfs_pin(req http.Request) http.Response {
	if req.data.len == 0 {
		return overlay_response(400, '{"error":"Request body required with cid field"}')
	}
	cid := json_field(req.data, 'cid')
	if cid.len == 0 {
		return overlay_response(400, '{"error":"cid field required"}')
	}
	if overlay_ffi_available {
		rc := C.echidna_ipfs_pin(cid.str, usize(cid.len))
		if rc == 0 {
			pin_count := C.echidna_ipfs_pin_count()
			return overlay_response(200, '{"pinned":true,"cid":"${esc(cid)}","total_pinned":${pin_count}}')
		}
		err := overlay_last_error()
		return overlay_response(500, '{"pinned":false,"cid":"${esc(cid)}","error":"${esc(err)}"}')
	}
	return overlay_response(200, '{"pinned":true,"cid":"${esc(cid)}","total_pinned":1}')
}

fn handle_ipfs_unpin(req http.Request) http.Response {
	if req.data.len == 0 {
		return overlay_response(400, '{"error":"Request body required with cid field"}')
	}
	cid := json_field(req.data, 'cid')
	if cid.len == 0 {
		return overlay_response(400, '{"error":"cid field required"}')
	}
	if overlay_ffi_available {
		rc := C.echidna_ipfs_unpin(cid.str, usize(cid.len))
		if rc == 0 {
			pin_count := C.echidna_ipfs_pin_count()
			return overlay_response(200, '{"unpinned":true,"cid":"${esc(cid)}","total_pinned":${pin_count}}')
		}
		err := overlay_last_error()
		return overlay_response(500, '{"unpinned":false,"cid":"${esc(cid)}","error":"${esc(err)}"}')
	}
	return overlay_response(200, '{"unpinned":true,"cid":"${esc(cid)}","total_pinned":0}')
}

fn handle_ipfs_dag_get(cid string) http.Response {
	if cid.len == 0 {
		return overlay_response(400, '{"error":"CID required in URL path"}')
	}
	if overlay_ffi_available {
		mut buf := [8192]u8{}
		mut buf_len := usize(8192)
		rc := C.echidna_ipfs_dag_get(cid.str, usize(cid.len), &buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			dag := unsafe { tos(&buf[0], int(buf_len)) }
			return overlay_response(200, dag)
		}
		err := overlay_last_error()
		return overlay_response(500, '{"cid":"${esc(cid)}","error":"${esc(err)}"}')
	}
	return overlay_response(200, '{"cid":"${esc(cid)}","links":0,"size":256,"data_size":128}')
}

// ============================================================================
// Ethereum Handlers (stubbed — Aerie future use)
// ============================================================================

fn handle_eth_connect(req http.Request) http.Response {
	config := if req.data.len > 0 { req.data } else { '{"rpc_url":"http://localhost:8545","chain_id":1337}' }
	if overlay_ffi_available {
		rc := C.echidna_eth_connect(config.str, usize(config.len))
		if rc == 0 {
			return overlay_response(200, '{"connected":true,"network":"ethereum","rpc_url":"http://localhost:8545","message":"Connected to Ethereum RPC (stubbed — Aerie future use)"}')
		}
		err := overlay_last_error()
		return overlay_response(500, '{"connected":false,"network":"ethereum","error":"${esc(err)}"}')
	}
	return overlay_response(200, '{"connected":true,"network":"ethereum","rpc_url":"http://localhost:8545","message":"Connected to Ethereum RPC (stub mode — Aerie future use)"}')
}

fn handle_eth_disconnect() http.Response {
	if overlay_ffi_available {
		C.echidna_eth_disconnect()
	}
	return overlay_response(200, '{"disconnected":true,"network":"ethereum","message":"Disconnected from Ethereum"}')
}

fn handle_eth_status() http.Response {
	if overlay_ffi_available {
		status := status_name(C.echidna_eth_status())
		return overlay_response(200, '{"network":"ethereum","status":"${status}","note":"Stubbed — awaiting Aerie integration"}')
	}
	return overlay_response(200, '{"network":"ethereum","status":"disconnected","note":"Stubbed — awaiting Aerie integration"}')
}

fn handle_eth_timestamp_proof(req http.Request) http.Response {
	if req.data.len == 0 {
		return overlay_response(400, '{"error":"Request body required with proof_hash field"}')
	}
	proof_hash := json_field(req.data, 'proof_hash')
	if proof_hash.len == 0 {
		return overlay_response(400, '{"error":"proof_hash field required (SHA3-256 hex string)"}')
	}
	if overlay_ffi_available {
		mut buf := [2048]u8{}
		mut buf_len := usize(2048)
		rc := C.echidna_eth_timestamp_proof(proof_hash.str, usize(proof_hash.len), &buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			result := unsafe { tos(&buf[0], int(buf_len)) }
			return overlay_response(200, result)
		}
		err := overlay_last_error()
		return overlay_response(500, '{"error":"${esc(err)}","proof_hash":"${esc(proof_hash)}"}')
	}
	return overlay_response(200, '{"tx_hash":"0xdeadbeef0123456789abcdef0123456789abcdef0123456789abcdef01234567","block_number":19000000,"timestamp":${time.now().unix()},"proof_hash":"${esc(proof_hash)}","chain_id":1,"status":"STUBBED","note":"Ethereum timestamping not yet implemented — awaiting Aerie integration"}')
}

fn handle_eth_verify_timestamp(req http.Request) http.Response {
	if req.data.len == 0 {
		return overlay_response(400, '{"error":"Request body required with tx_hash field"}')
	}
	tx_hash := json_field(req.data, 'tx_hash')
	if tx_hash.len == 0 {
		return overlay_response(400, '{"error":"tx_hash field required (0x-prefixed hex string)"}')
	}
	if overlay_ffi_available {
		mut buf := [2048]u8{}
		mut buf_len := usize(2048)
		rc := C.echidna_eth_verify_timestamp(tx_hash.str, usize(tx_hash.len), &buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			result := unsafe { tos(&buf[0], int(buf_len)) }
			return overlay_response(200, result)
		}
		err := overlay_last_error()
		return overlay_response(500, '{"error":"${esc(err)}","tx_hash":"${esc(tx_hash)}"}')
	}
	return overlay_response(200, '{"verified":true,"tx_hash":"${esc(tx_hash)}","proof_hash":"sha3-256:stub","block_number":19000000,"timestamp":${time.now().unix()},"confirmations":100,"status":"STUBBED"}')
}

// --- Helpers ---

fn esc(s string) string {
	return s.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n').replace('\t', '\\t')
}

fn json_field(data string, key string) string {
	needle := '"${key}":'
	idx := data.index(needle) or { return '' }
	tail := data[idx + needle.len..].trim_space()
	if tail.len == 0 || tail[0] != `"` {
		return ''
	}
	end := tail[1..].index('"') or { return '' }
	return tail[1..end + 1]
}

fn json_field_or(data string, key string, default_val string) string {
	val := json_field(data, key)
	if val.len == 0 {
		return default_val
	}
	return val
}

fn json_field_int(data string, key string) int {
	needle := '"${key}":'
	idx := data.index(needle) or { return 0 }
	tail := data[idx + needle.len..].trim_space()
	if tail.len == 0 {
		return 0
	}
	mut end := 0
	for i, c in tail {
		if c >= `0` && c <= `9` {
			end = i + 1
		} else if end > 0 {
			break
		}
	}
	if end == 0 {
		return 0
	}
	return tail[..end].int()
}
