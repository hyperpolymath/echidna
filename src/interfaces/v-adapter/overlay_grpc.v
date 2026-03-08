// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// ECHIDNA Overlay Network gRPC-Web API Gateway
//
// Exposes Tor, IPFS, and Ethereum overlay network operations via gRPC-style
// RPC (JSON-over-HTTP transport, gRPC-Web compatible) on port 8104:
//
//   Unified:
//     POST /echidna.OverlayService/Health    — overlay subsystem health
//     POST /echidna.OverlayService/Status    — combined status of all networks
//     POST /echidna.OverlayService/Version   — overlay module version
//
//   Tor:
//     POST /echidna.OverlayService/TorConnect               — connect to Tor
//     POST /echidna.OverlayService/TorDisconnect             — disconnect from Tor
//     POST /echidna.OverlayService/TorStatus                 — Tor connection status
//     POST /echidna.OverlayService/TorCreateHiddenService    — create hidden service
//     POST /echidna.OverlayService/TorDestroyHiddenService   — destroy hidden service
//     POST /echidna.OverlayService/TorListCircuits           — list active circuits
//     POST /echidna.OverlayService/TorGetCircuit             — get circuit details
//     POST /echidna.OverlayService/TorResolve                — resolve via Tor
//
//   IPFS:
//     POST /echidna.OverlayService/IpfsConnect      — connect to IPFS
//     POST /echidna.OverlayService/IpfsDisconnect   — disconnect from IPFS
//     POST /echidna.OverlayService/IpfsStatus       — IPFS connection status
//     POST /echidna.OverlayService/IpfsAdd           — add content, returns CID
//     POST /echidna.OverlayService/IpfsCat           — retrieve content by CID
//     POST /echidna.OverlayService/IpfsPin           — pin content by CID
//     POST /echidna.OverlayService/IpfsUnpin         — unpin content by CID
//     POST /echidna.OverlayService/IpfsDagGet        — get DAG node
//
//   Ethereum (stubbed):
//     POST /echidna.OverlayService/EthConnect           — connect to Ethereum
//     POST /echidna.OverlayService/EthDisconnect        — disconnect
//     POST /echidna.OverlayService/EthStatus             — connection status
//     POST /echidna.OverlayService/EthTimestampProof     — anchor proof on-chain
//     POST /echidna.OverlayService/EthVerifyTimestamp    — verify anchored timestamp
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

__global overlay_ffi_available = false
__global overlay_ffi_initialised = false

fn init_overlay_ffi() {
	ptr := C.echidna_overlay_version()
	if ptr != unsafe { nil } {
		ver := unsafe { cstring_to_vstring(ptr) }
		if ver.len > 0 {
			overlay_ffi_available = true
			overlay_ffi_initialised = true
			println('  FFI: linked to libechidna_overlay.so v${ver} (live mode)')
			return
		}
	}
	overlay_ffi_available = false
	println('  FFI: overlay library not available (stub mode)')
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

fn grpc_response(status_code int, body string) http.Response {
	mut header := http.new_header(key: .content_type, value: 'application/grpc+json')
	if overlay_ffi_available {
		header.add_custom('X-Overlay-Mode', 'live') or {}
	} else {
		header.add_custom('X-Overlay-Mode', 'stub') or {}
	}
	header.add_custom('grpc-status', '0') or {}
	return http.new_response(
		status: unsafe { http.Status(status_code) }
		header: header
		body: body
	)
}

// --- Handler ---

struct OverlayGRPCHandler {
	port int
}

pub fn (mut h OverlayGRPCHandler) handle(req http.Request) http.Response {
	if req.method != .post {
		return grpc_response(405, '{"error":"POST required for RPC calls"}')
	}

	path := req.url.all_before('?')
	return match path {
		// Unified
		'/echidna.OverlayService/Health' { rpc_health() }
		'/echidna.OverlayService/Status' { rpc_status() }
		'/echidna.OverlayService/Version' { rpc_version() }
		// Tor
		'/echidna.OverlayService/TorConnect' { rpc_tor_connect(req) }
		'/echidna.OverlayService/TorDisconnect' { rpc_tor_disconnect() }
		'/echidna.OverlayService/TorStatus' { rpc_tor_status() }
		'/echidna.OverlayService/TorCreateHiddenService' { rpc_tor_create_hs(req) }
		'/echidna.OverlayService/TorDestroyHiddenService' { rpc_tor_destroy_hs(req) }
		'/echidna.OverlayService/TorListCircuits' { rpc_tor_list_circuits() }
		'/echidna.OverlayService/TorGetCircuit' { rpc_tor_get_circuit(req) }
		'/echidna.OverlayService/TorResolve' { rpc_tor_resolve(req) }
		// IPFS
		'/echidna.OverlayService/IpfsConnect' { rpc_ipfs_connect(req) }
		'/echidna.OverlayService/IpfsDisconnect' { rpc_ipfs_disconnect() }
		'/echidna.OverlayService/IpfsStatus' { rpc_ipfs_status() }
		'/echidna.OverlayService/IpfsAdd' { rpc_ipfs_add(req) }
		'/echidna.OverlayService/IpfsCat' { rpc_ipfs_cat(req) }
		'/echidna.OverlayService/IpfsPin' { rpc_ipfs_pin(req) }
		'/echidna.OverlayService/IpfsUnpin' { rpc_ipfs_unpin(req) }
		'/echidna.OverlayService/IpfsDagGet' { rpc_ipfs_dag_get(req) }
		// Ethereum
		'/echidna.OverlayService/EthConnect' { rpc_eth_connect(req) }
		'/echidna.OverlayService/EthDisconnect' { rpc_eth_disconnect() }
		'/echidna.OverlayService/EthStatus' { rpc_eth_status() }
		'/echidna.OverlayService/EthTimestampProof' { rpc_eth_timestamp(req) }
		'/echidna.OverlayService/EthVerifyTimestamp' { rpc_eth_verify(req) }
		else {
			grpc_response(404, '{"error":"Unknown method: ${esc(path)}","service":"echidna.OverlayService"}')
		}
	}
}

// --- Server ---

pub struct Server {
pub mut:
	port int
}

pub fn new_server(port int) &Server {
	return &Server{port: port}
}

pub fn (s Server) start() {
	println('ECHIDNA Overlay gRPC-Web API Gateway starting on port ${s.port}...')
	init_overlay_ffi()
	println('  === Unified ===')
	println('  POST /echidna.OverlayService/Health')
	println('  POST /echidna.OverlayService/Status')
	println('  POST /echidna.OverlayService/Version')
	println('  === Tor (8 RPCs) ===')
	println('  POST /echidna.OverlayService/Tor{Connect,Disconnect,Status,CreateHiddenService,...}')
	println('  === IPFS (8 RPCs) ===')
	println('  POST /echidna.OverlayService/Ipfs{Connect,Disconnect,Status,Add,Cat,Pin,Unpin,DagGet}')
	println('  === Ethereum (5 RPCs, stubbed) ===')
	println('  POST /echidna.OverlayService/Eth{Connect,Disconnect,Status,TimestampProof,VerifyTimestamp}')
	println('  (JSON-over-HTTP transport, gRPC-Web compatible)')
	mut server := http.Server{
		addr: ':${s.port}'
		handler: &OverlayGRPCHandler{port: s.port}
	}
	server.listen_and_serve()
}

fn main() {
	mut s := new_server(8104)
	s.start()
}

// ============================================================================
// Unified RPCs
// ============================================================================

fn rpc_health() http.Response {
	now := time.now()
	if overlay_ffi_available {
		ver := overlay_version()
		tor := status_name(C.echidna_tor_status())
		ipfs := status_name(C.echidna_ipfs_status())
		eth := status_name(C.echidna_eth_status())
		return grpc_response(200, '{"status":"SERVING","service":"echidna-overlay-grpc","version":"${ver}","tor":"${tor}","ipfs":"${ipfs}","ethereum":"${eth}","uptime_seconds":${now.unix()},"ffi_mode":"live"}')
	}
	return grpc_response(200, '{"status":"SERVING","service":"echidna-overlay-grpc","version":"1.0.0","tor":"disconnected","ipfs":"disconnected","ethereum":"disconnected","uptime_seconds":${now.unix()},"ffi_mode":"stub"}')
}

fn rpc_status() http.Response {
	if overlay_ffi_available {
		tor := status_name(C.echidna_tor_status())
		ipfs := status_name(C.echidna_ipfs_status())
		eth := status_name(C.echidna_eth_status())
		tor_hs := C.echidna_tor_hidden_service_count()
		ipfs_pins := C.echidna_ipfs_pin_count()
		return grpc_response(200, '{"tor":{"status":"${tor}","hidden_services":${tor_hs}},"ipfs":{"status":"${ipfs}","pinned_items":${ipfs_pins}},"ethereum":{"status":"${eth}","note":"Stubbed"}}')
	}
	return grpc_response(200, '{"tor":{"status":"disconnected","hidden_services":0},"ipfs":{"status":"disconnected","pinned_items":0},"ethereum":{"status":"disconnected","note":"Stubbed"}}')
}

fn rpc_version() http.Response {
	if overlay_ffi_available {
		return grpc_response(200, '{"version":"${overlay_version()}"}')
	}
	return grpc_response(200, '{"version":"1.0.0"}')
}

// ============================================================================
// Tor RPCs
// ============================================================================

fn rpc_tor_connect(req http.Request) http.Response {
	config := if req.data.len > 0 { req.data } else { '{"control_port":9051}' }
	if overlay_ffi_available {
		rc := C.echidna_tor_connect(config.str, usize(config.len))
		if rc == 0 {
			return grpc_response(200, '{"connected":true,"network":"tor","control_port":9051,"socks_port":9050}')
		}
		return grpc_response(500, '{"connected":false,"error":"${esc(overlay_last_error())}"}')
	}
	return grpc_response(200, '{"connected":true,"network":"tor","control_port":9051,"socks_port":9050}')
}

fn rpc_tor_disconnect() http.Response {
	if overlay_ffi_available {
		C.echidna_tor_disconnect()
	}
	return grpc_response(200, '{"disconnected":true,"network":"tor"}')
}

fn rpc_tor_status() http.Response {
	if overlay_ffi_available {
		return grpc_response(200, '{"network":"tor","status":"${status_name(C.echidna_tor_status())}","hidden_services":${C.echidna_tor_hidden_service_count()}}')
	}
	return grpc_response(200, '{"network":"tor","status":"disconnected","hidden_services":0}')
}

fn rpc_tor_create_hs(req http.Request) http.Response {
	port := json_field_int(req.data, 'port')
	target_port := json_field_int(req.data, 'target_port')
	if port <= 0 || target_port <= 0 {
		return grpc_response(400, '{"error":"port and target_port required"}')
	}
	if overlay_ffi_available {
		mut buf := [128]u8{}
		mut buf_len := usize(128)
		rc := C.echidna_tor_create_hidden_service(port, target_port, &buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			onion := unsafe { tos(&buf[0], int(buf_len)) }
			return grpc_response(200, '{"created":true,"onion_address":"${esc(onion)}","port":${port},"target_port":${target_port},"active_services":${C.echidna_tor_hidden_service_count()}}')
		}
		return grpc_response(500, '{"created":false,"error":"${esc(overlay_last_error())}"}')
	}
	return grpc_response(200, '{"created":true,"onion_address":"echidna2fproof7verify3trust8secure4formal5check6valid.onion","port":${port},"target_port":${target_port},"active_services":1}')
}

fn rpc_tor_destroy_hs(req http.Request) http.Response {
	onion := json_field(req.data, 'onion_address')
	if onion.len == 0 {
		return grpc_response(400, '{"error":"onion_address required"}')
	}
	if overlay_ffi_available {
		rc := C.echidna_tor_destroy_hidden_service(onion.str, usize(onion.len))
		if rc == 0 {
			return grpc_response(200, '{"destroyed":true,"onion_address":"${esc(onion)}","remaining_services":${C.echidna_tor_hidden_service_count()}}')
		}
		return grpc_response(500, '{"destroyed":false,"error":"${esc(overlay_last_error())}"}')
	}
	return grpc_response(200, '{"destroyed":true,"onion_address":"${esc(onion)}","remaining_services":0}')
}

fn rpc_tor_list_circuits() http.Response {
	if overlay_ffi_available {
		mut buf := [8192]u8{}
		mut buf_len := usize(8192)
		rc := C.echidna_tor_list_circuits(&buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			return grpc_response(200, '{"network":"tor","circuits":${unsafe { tos(&buf[0], int(buf_len)) }}}')
		}
		return grpc_response(500, '{"error":"${esc(overlay_last_error())}"}')
	}
	return grpc_response(200, '{"network":"tor","circuits":[{"circuit_id":1,"status":"BUILT","hop_count":3,"purpose":"GENERAL"}]}')
}

fn rpc_tor_get_circuit(req http.Request) http.Response {
	circuit_id := json_field_int(req.data, 'circuit_id')
	if overlay_ffi_available {
		mut buf := [8192]u8{}
		mut buf_len := usize(8192)
		rc := C.echidna_tor_get_circuit(circuit_id, &buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			return grpc_response(200, unsafe { tos(&buf[0], int(buf_len)) })
		}
		return grpc_response(500, '{"error":"${esc(overlay_last_error())}"}')
	}
	return grpc_response(200, '{"circuit_id":${circuit_id},"status":"BUILT","path":[{"fingerprint":"AAAA...","nickname":"Guard1","country":"DE","is_exit":false},{"fingerprint":"BBBB...","nickname":"Middle1","country":"NL","is_exit":false},{"fingerprint":"CCCC...","nickname":"Exit1","country":"SE","is_exit":true}],"purpose":"GENERAL","time_created":"${time.now().format_rfc3339()}"}')
}

fn rpc_tor_resolve(req http.Request) http.Response {
	hostname := json_field(req.data, 'hostname')
	if hostname.len == 0 {
		return grpc_response(400, '{"error":"hostname required"}')
	}
	if overlay_ffi_available {
		mut buf := [256]u8{}
		mut buf_len := usize(256)
		rc := C.echidna_tor_resolve(hostname.str, usize(hostname.len), &buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			return grpc_response(200, '{"hostname":"${esc(hostname)}","resolved":"${unsafe { tos(&buf[0], int(buf_len)) }}","via":"tor-socks5"}')
		}
		return grpc_response(500, '{"hostname":"${esc(hostname)}","error":"${esc(overlay_last_error())}"}')
	}
	return grpc_response(200, '{"hostname":"${esc(hostname)}","resolved":"198.51.100.42","via":"tor-socks5"}')
}

// ============================================================================
// IPFS RPCs
// ============================================================================

fn rpc_ipfs_connect(req http.Request) http.Response {
	config := if req.data.len > 0 { req.data } else { '{"api_port":5001}' }
	if overlay_ffi_available {
		rc := C.echidna_ipfs_connect(config.str, usize(config.len))
		if rc == 0 {
			return grpc_response(200, '{"connected":true,"network":"ipfs","api_port":5001,"gateway_port":8080}')
		}
		return grpc_response(500, '{"connected":false,"error":"${esc(overlay_last_error())}"}')
	}
	return grpc_response(200, '{"connected":true,"network":"ipfs","api_port":5001,"gateway_port":8080}')
}

fn rpc_ipfs_disconnect() http.Response {
	if overlay_ffi_available {
		C.echidna_ipfs_disconnect()
	}
	return grpc_response(200, '{"disconnected":true,"network":"ipfs"}')
}

fn rpc_ipfs_status() http.Response {
	if overlay_ffi_available {
		return grpc_response(200, '{"network":"ipfs","status":"${status_name(C.echidna_ipfs_status())}","pinned_items":${C.echidna_ipfs_pin_count()}}')
	}
	return grpc_response(200, '{"network":"ipfs","status":"disconnected","pinned_items":0}')
}

fn rpc_ipfs_add(req http.Request) http.Response {
	data := json_field(req.data, 'data')
	if data.len == 0 {
		return grpc_response(400, '{"error":"data required"}')
	}
	if overlay_ffi_available {
		mut cid_buf := [256]u8{}
		mut cid_len := usize(256)
		rc := C.echidna_ipfs_add(data.str, usize(data.len), &cid_buf[0], &cid_len)
		if rc == 0 && cid_len > 0 {
			cid := unsafe { tos(&cid_buf[0], int(cid_len)) }
			return grpc_response(200, '{"added":true,"cid":"${esc(cid)}","size":${data.len}}')
		}
		return grpc_response(500, '{"added":false,"error":"${esc(overlay_last_error())}"}')
	}
	return grpc_response(200, '{"added":true,"cid":"bafkreihdwdcefgh4dqkjv67uzcmw7ojee6xedzdetojuzjevtenrqpc","size":${data.len}}')
}

fn rpc_ipfs_cat(req http.Request) http.Response {
	cid := json_field(req.data, 'cid')
	if cid.len == 0 {
		return grpc_response(400, '{"error":"cid required"}')
	}
	if overlay_ffi_available {
		mut buf := [65536]u8{}
		mut buf_len := usize(65536)
		rc := C.echidna_ipfs_cat(cid.str, usize(cid.len), &buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			content := unsafe { tos(&buf[0], int(buf_len)) }
			return grpc_response(200, '{"cid":"${esc(cid)}","content":"${esc(content)}","size":${buf_len}}')
		}
		return grpc_response(500, '{"cid":"${esc(cid)}","error":"${esc(overlay_last_error())}"}')
	}
	return grpc_response(200, '{"cid":"${esc(cid)}","content":"(* ECHIDNA proof certificate — retrieved from IPFS *)","size":54}')
}

fn rpc_ipfs_pin(req http.Request) http.Response {
	cid := json_field(req.data, 'cid')
	if cid.len == 0 {
		return grpc_response(400, '{"error":"cid required"}')
	}
	if overlay_ffi_available {
		rc := C.echidna_ipfs_pin(cid.str, usize(cid.len))
		if rc == 0 {
			return grpc_response(200, '{"pinned":true,"cid":"${esc(cid)}","total_pinned":${C.echidna_ipfs_pin_count()}}')
		}
		return grpc_response(500, '{"pinned":false,"error":"${esc(overlay_last_error())}"}')
	}
	return grpc_response(200, '{"pinned":true,"cid":"${esc(cid)}","total_pinned":1}')
}

fn rpc_ipfs_unpin(req http.Request) http.Response {
	cid := json_field(req.data, 'cid')
	if cid.len == 0 {
		return grpc_response(400, '{"error":"cid required"}')
	}
	if overlay_ffi_available {
		rc := C.echidna_ipfs_unpin(cid.str, usize(cid.len))
		if rc == 0 {
			return grpc_response(200, '{"unpinned":true,"cid":"${esc(cid)}","total_pinned":${C.echidna_ipfs_pin_count()}}')
		}
		return grpc_response(500, '{"unpinned":false,"error":"${esc(overlay_last_error())}"}')
	}
	return grpc_response(200, '{"unpinned":true,"cid":"${esc(cid)}","total_pinned":0}')
}

fn rpc_ipfs_dag_get(req http.Request) http.Response {
	cid := json_field(req.data, 'cid')
	if cid.len == 0 {
		return grpc_response(400, '{"error":"cid required"}')
	}
	if overlay_ffi_available {
		mut buf := [8192]u8{}
		mut buf_len := usize(8192)
		rc := C.echidna_ipfs_dag_get(cid.str, usize(cid.len), &buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			return grpc_response(200, unsafe { tos(&buf[0], int(buf_len)) })
		}
		return grpc_response(500, '{"cid":"${esc(cid)}","error":"${esc(overlay_last_error())}"}')
	}
	return grpc_response(200, '{"cid":"${esc(cid)}","links":0,"size":256,"data_size":128}')
}

// ============================================================================
// Ethereum RPCs (stubbed)
// ============================================================================

fn rpc_eth_connect(req http.Request) http.Response {
	config := if req.data.len > 0 { req.data } else { '{"rpc_url":"http://localhost:8545","chain_id":1337}' }
	if overlay_ffi_available {
		rc := C.echidna_eth_connect(config.str, usize(config.len))
		if rc == 0 {
			return grpc_response(200, '{"connected":true,"network":"ethereum","note":"Stubbed — Aerie future use"}')
		}
		return grpc_response(500, '{"connected":false,"error":"${esc(overlay_last_error())}"}')
	}
	return grpc_response(200, '{"connected":true,"network":"ethereum","note":"Stubbed — Aerie future use"}')
}

fn rpc_eth_disconnect() http.Response {
	if overlay_ffi_available {
		C.echidna_eth_disconnect()
	}
	return grpc_response(200, '{"disconnected":true,"network":"ethereum"}')
}

fn rpc_eth_status() http.Response {
	if overlay_ffi_available {
		return grpc_response(200, '{"network":"ethereum","status":"${status_name(C.echidna_eth_status())}","note":"Stubbed"}')
	}
	return grpc_response(200, '{"network":"ethereum","status":"disconnected","note":"Stubbed"}')
}

fn rpc_eth_timestamp(req http.Request) http.Response {
	proof_hash := json_field(req.data, 'proof_hash')
	if proof_hash.len == 0 {
		return grpc_response(400, '{"error":"proof_hash required"}')
	}
	if overlay_ffi_available {
		mut buf := [2048]u8{}
		mut buf_len := usize(2048)
		rc := C.echidna_eth_timestamp_proof(proof_hash.str, usize(proof_hash.len), &buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			return grpc_response(200, unsafe { tos(&buf[0], int(buf_len)) })
		}
		return grpc_response(500, '{"error":"${esc(overlay_last_error())}"}')
	}
	return grpc_response(200, '{"tx_hash":"0xdeadbeef0123456789abcdef0123456789abcdef0123456789abcdef01234567","block_number":19000000,"timestamp":${time.now().unix()},"proof_hash":"${esc(proof_hash)}","status":"STUBBED"}')
}

fn rpc_eth_verify(req http.Request) http.Response {
	tx_hash := json_field(req.data, 'tx_hash')
	if tx_hash.len == 0 {
		return grpc_response(400, '{"error":"tx_hash required"}')
	}
	if overlay_ffi_available {
		mut buf := [2048]u8{}
		mut buf_len := usize(2048)
		rc := C.echidna_eth_verify_timestamp(tx_hash.str, usize(tx_hash.len), &buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			return grpc_response(200, unsafe { tos(&buf[0], int(buf_len)) })
		}
		return grpc_response(500, '{"error":"${esc(overlay_last_error())}"}')
	}
	return grpc_response(200, '{"verified":true,"tx_hash":"${esc(tx_hash)}","proof_hash":"sha3-256:stub","block_number":19000000,"timestamp":${time.now().unix()},"status":"STUBBED"}')
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
