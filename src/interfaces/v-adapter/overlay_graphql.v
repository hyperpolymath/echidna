// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// ECHIDNA Overlay Network GraphQL API Gateway
//
// Exposes Tor, IPFS, and Ethereum overlay network operations via GraphQL on port 8105:
//
//   Queries:
//     overlayHealth { healthy tor ipfs ethereum version ffiMode }
//     overlayStatus { tor { status hiddenServices } ipfs { status pinnedItems } ethereum { status } }
//     overlayVersion { version }
//     torStatus { network status hiddenServices }
//     torCircuits { circuitId status hopCount purpose }
//     torCircuit(id: Int) { circuitId status path { fingerprint nickname country isExit } }
//     ipfsStatus { network status pinnedItems }
//     ethStatus { network status note }
//
//   Mutations:
//     torConnect(config: JSON) { connected network }
//     torDisconnect { disconnected }
//     torCreateHiddenService(port: Int, targetPort: Int) { created onionAddress activeServices }
//     torDestroyHiddenService(onionAddress: String) { destroyed remainingServices }
//     torResolve(hostname: String) { hostname resolved via }
//     ipfsConnect(config: JSON) { connected network }
//     ipfsDisconnect { disconnected }
//     ipfsAdd(data: String, contentType: String) { added cid size }
//     ipfsCat(cid: String) { cid content size }
//     ipfsPin(cid: String) { pinned totalPinned }
//     ipfsUnpin(cid: String) { unpinned totalPinned }
//     ipfsDagGet(cid: String) { cid links size }
//     ethConnect(config: JSON) { connected note }
//     ethDisconnect { disconnected }
//     ethTimestampProof(proofHash: String) { txHash blockNumber timestamp status }
//     ethVerifyTimestamp(txHash: String) { verified proofHash blockNumber timestamp status }
//
//   GET /graphql — GraphiQL playground
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

fn gql_response(status_code int, body string) http.Response {
	mut header := http.new_header(key: .content_type, value: 'application/json')
	if overlay_ffi_available {
		header.add_custom('X-Overlay-Mode', 'live') or {}
	} else {
		header.add_custom('X-Overlay-Mode', 'stub') or {}
	}
	return http.new_response(
		status: unsafe { http.Status(status_code) }
		header: header
		body: body
	)
}

// --- Handler ---

struct OverlayGraphQLHandler {
	port int
}

pub fn (mut h OverlayGraphQLHandler) handle(req http.Request) http.Response {
	path := req.url.all_before('?')

	// GET /graphql — serve GraphiQL playground
	if path == '/graphql' && req.method == .get {
		return serve_graphiql()
	}
	// POST /graphql — resolve query/mutation
	if path == '/graphql' && req.method == .post {
		query := json_field(req.data, 'query')
		if query.len == 0 {
			return gql_response(400, '{"errors":[{"message":"query field required in POST body"}]}')
		}
		return resolve(query, req.data)
	}
	// GET / — redirect to GraphiQL
	if path == '/' && req.method == .get {
		return gql_response(200, '{"service":"echidna-overlay-graphql","playground":"/graphql"}')
	}

	return gql_response(404, '{"errors":[{"message":"Use POST /graphql for queries, GET /graphql for GraphiQL"}]}')
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
	println('ECHIDNA Overlay GraphQL API Gateway starting on port ${s.port}...')
	init_overlay_ffi()
	println('  POST /graphql — query and mutation endpoint')
	println('  GET  /graphql — GraphiQL interactive playground')
	println('  Queries: overlayHealth, overlayStatus, overlayVersion, torStatus, torCircuits, ipfsStatus, ethStatus')
	println('  Mutations: tor{Connect,Disconnect,CreateHiddenService,...}, ipfs{Connect,Add,Cat,Pin,...}, eth{Connect,TimestampProof,...}')
	mut server := http.Server{
		addr: ':${s.port}'
		handler: &OverlayGraphQLHandler{port: s.port}
	}
	server.listen_and_serve()
}

fn main() {
	mut s := new_server(8105)
	s.start()
}

// ============================================================================
// Resolver Dispatch
// ============================================================================

fn resolve(query string, data string) http.Response {
	// Mutations (check first — they modify state)
	if query.contains('torConnect') { return resolve_tor_connect(data) }
	if query.contains('torDisconnect') { return resolve_tor_disconnect() }
	if query.contains('torCreateHiddenService') { return resolve_tor_create_hs(query) }
	if query.contains('torDestroyHiddenService') { return resolve_tor_destroy_hs(query) }
	if query.contains('torResolve') { return resolve_tor_resolve(query) }
	if query.contains('ipfsConnect') { return resolve_ipfs_connect(data) }
	if query.contains('ipfsDisconnect') { return resolve_ipfs_disconnect() }
	if query.contains('ipfsAdd') { return resolve_ipfs_add(query) }
	if query.contains('ipfsCat') { return resolve_ipfs_cat(query) }
	if query.contains('ipfsPin(') { return resolve_ipfs_pin(query) }
	if query.contains('ipfsUnpin') { return resolve_ipfs_unpin(query) }
	if query.contains('ipfsDagGet') { return resolve_ipfs_dag_get(query) }
	if query.contains('ethConnect') { return resolve_eth_connect(data) }
	if query.contains('ethDisconnect') { return resolve_eth_disconnect() }
	if query.contains('ethTimestampProof') { return resolve_eth_timestamp(query) }
	if query.contains('ethVerifyTimestamp') { return resolve_eth_verify(query) }

	// Queries
	if query.contains('overlayHealth') { return resolve_health() }
	if query.contains('overlayStatus') { return resolve_status() }
	if query.contains('overlayVersion') { return resolve_version() }
	if query.contains('torCircuit(') { return resolve_tor_circuit(query) }
	if query.contains('torCircuits') { return resolve_tor_circuits() }
	if query.contains('torStatus') { return resolve_tor_status() }
	if query.contains('ipfsStatus') { return resolve_ipfs_status() }
	if query.contains('ethStatus') { return resolve_eth_status() }
	if query.contains('__schema') { return resolve_schema() }

	return gql_response(200, '{"errors":[{"message":"Unknown query/mutation. Use overlayHealth, overlayStatus, torConnect, ipfsAdd, ethTimestampProof, etc."}]}')
}

// ============================================================================
// Query Resolvers
// ============================================================================

fn resolve_health() http.Response {
	now := time.now()
	if overlay_ffi_available {
		ver := overlay_version()
		tor := status_name(C.echidna_tor_status())
		ipfs := status_name(C.echidna_ipfs_status())
		eth := status_name(C.echidna_eth_status())
		return gql_response(200, '{"data":{"overlayHealth":{"healthy":true,"service":"echidna-overlay-graphql","version":"${ver}","tor":"${tor}","ipfs":"${ipfs}","ethereum":"${eth}","uptimeSeconds":${now.unix()},"ffiMode":"live"}}}')
	}
	return gql_response(200, '{"data":{"overlayHealth":{"healthy":true,"service":"echidna-overlay-graphql","version":"1.0.0","tor":"disconnected","ipfs":"disconnected","ethereum":"disconnected","uptimeSeconds":${now.unix()},"ffiMode":"stub"}}}')
}

fn resolve_status() http.Response {
	if overlay_ffi_available {
		tor := status_name(C.echidna_tor_status())
		ipfs := status_name(C.echidna_ipfs_status())
		eth := status_name(C.echidna_eth_status())
		return gql_response(200, '{"data":{"overlayStatus":{"tor":{"status":"${tor}","hiddenServices":${C.echidna_tor_hidden_service_count()}},"ipfs":{"status":"${ipfs}","pinnedItems":${C.echidna_ipfs_pin_count()}},"ethereum":{"status":"${eth}","note":"Stubbed"}}}}')
	}
	return gql_response(200, '{"data":{"overlayStatus":{"tor":{"status":"disconnected","hiddenServices":0},"ipfs":{"status":"disconnected","pinnedItems":0},"ethereum":{"status":"disconnected","note":"Stubbed"}}}}')
}

fn resolve_version() http.Response {
	if overlay_ffi_available {
		return gql_response(200, '{"data":{"overlayVersion":{"version":"${overlay_version()}"}}}')
	}
	return gql_response(200, '{"data":{"overlayVersion":{"version":"1.0.0"}}}')
}

fn resolve_tor_status() http.Response {
	if overlay_ffi_available {
		return gql_response(200, '{"data":{"torStatus":{"network":"tor","status":"${status_name(C.echidna_tor_status())}","hiddenServices":${C.echidna_tor_hidden_service_count()}}}}')
	}
	return gql_response(200, '{"data":{"torStatus":{"network":"tor","status":"disconnected","hiddenServices":0}}}')
}

fn resolve_tor_circuits() http.Response {
	if overlay_ffi_available {
		mut buf := [8192]u8{}
		mut buf_len := usize(8192)
		rc := C.echidna_tor_list_circuits(&buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			return gql_response(200, '{"data":{"torCircuits":${unsafe { tos(&buf[0], int(buf_len)) }}}}')
		}
	}
	return gql_response(200, '{"data":{"torCircuits":[{"circuitId":1,"status":"BUILT","hopCount":3,"purpose":"GENERAL"}]}}')
}

fn resolve_tor_circuit(query string) http.Response {
	id := extract_int_arg(query, 'id')
	if overlay_ffi_available {
		mut buf := [8192]u8{}
		mut buf_len := usize(8192)
		rc := C.echidna_tor_get_circuit(id, &buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			return gql_response(200, '{"data":{"torCircuit":${unsafe { tos(&buf[0], int(buf_len)) }}}}')
		}
	}
	return gql_response(200, '{"data":{"torCircuit":{"circuitId":${id},"status":"BUILT","path":[{"fingerprint":"AAAA...","nickname":"Guard1","country":"DE","isExit":false}],"purpose":"GENERAL"}}}')
}

fn resolve_ipfs_status() http.Response {
	if overlay_ffi_available {
		return gql_response(200, '{"data":{"ipfsStatus":{"network":"ipfs","status":"${status_name(C.echidna_ipfs_status())}","pinnedItems":${C.echidna_ipfs_pin_count()}}}}')
	}
	return gql_response(200, '{"data":{"ipfsStatus":{"network":"ipfs","status":"disconnected","pinnedItems":0}}}')
}

fn resolve_eth_status() http.Response {
	if overlay_ffi_available {
		return gql_response(200, '{"data":{"ethStatus":{"network":"ethereum","status":"${status_name(C.echidna_eth_status())}","note":"Stubbed — Aerie future use"}}}')
	}
	return gql_response(200, '{"data":{"ethStatus":{"network":"ethereum","status":"disconnected","note":"Stubbed — Aerie future use"}}}')
}

fn resolve_schema() http.Response {
	return gql_response(200, '{"data":{"__schema":{"queryType":{"name":"Query"},"mutationType":{"name":"Mutation"},"types":[{"name":"Query","fields":["overlayHealth","overlayStatus","overlayVersion","torStatus","torCircuits","torCircuit","ipfsStatus","ethStatus"]},{"name":"Mutation","fields":["torConnect","torDisconnect","torCreateHiddenService","torDestroyHiddenService","torResolve","ipfsConnect","ipfsDisconnect","ipfsAdd","ipfsCat","ipfsPin","ipfsUnpin","ipfsDagGet","ethConnect","ethDisconnect","ethTimestampProof","ethVerifyTimestamp"]}]}}}')
}

// ============================================================================
// Mutation Resolvers — Tor
// ============================================================================

fn resolve_tor_connect(data string) http.Response {
	config := if data.len > 0 { data } else { '{"control_port":9051}' }
	if overlay_ffi_available {
		rc := C.echidna_tor_connect(config.str, usize(config.len))
		if rc == 0 {
			return gql_response(200, '{"data":{"torConnect":{"connected":true,"network":"tor","controlPort":9051,"socksPort":9050}}}')
		}
		return gql_response(200, '{"errors":[{"message":"Tor connect failed: ${esc(overlay_last_error())}"}]}')
	}
	return gql_response(200, '{"data":{"torConnect":{"connected":true,"network":"tor","controlPort":9051,"socksPort":9050}}}')
}

fn resolve_tor_disconnect() http.Response {
	if overlay_ffi_available {
		C.echidna_tor_disconnect()
	}
	return gql_response(200, '{"data":{"torDisconnect":{"disconnected":true,"network":"tor"}}}')
}

fn resolve_tor_create_hs(query string) http.Response {
	port := extract_int_arg(query, 'port')
	target_port := extract_int_arg(query, 'targetPort')
	if port <= 0 || target_port <= 0 {
		return gql_response(200, '{"errors":[{"message":"port and targetPort required for torCreateHiddenService"}]}')
	}
	if overlay_ffi_available {
		mut buf := [128]u8{}
		mut buf_len := usize(128)
		rc := C.echidna_tor_create_hidden_service(port, target_port, &buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			onion := unsafe { tos(&buf[0], int(buf_len)) }
			return gql_response(200, '{"data":{"torCreateHiddenService":{"created":true,"onionAddress":"${esc(onion)}","port":${port},"targetPort":${target_port},"activeServices":${C.echidna_tor_hidden_service_count()}}}}')
		}
		return gql_response(200, '{"errors":[{"message":"${esc(overlay_last_error())}"}]}')
	}
	return gql_response(200, '{"data":{"torCreateHiddenService":{"created":true,"onionAddress":"echidna2fproof7verify3trust8secure4formal5check6valid.onion","port":${port},"targetPort":${target_port},"activeServices":1}}}')
}

fn resolve_tor_destroy_hs(query string) http.Response {
	onion := extract_arg(query, 'onionAddress')
	if onion.len == 0 {
		return gql_response(200, '{"errors":[{"message":"onionAddress required"}]}')
	}
	if overlay_ffi_available {
		rc := C.echidna_tor_destroy_hidden_service(onion.str, usize(onion.len))
		if rc == 0 {
			return gql_response(200, '{"data":{"torDestroyHiddenService":{"destroyed":true,"onionAddress":"${esc(onion)}","remainingServices":${C.echidna_tor_hidden_service_count()}}}}')
		}
		return gql_response(200, '{"errors":[{"message":"${esc(overlay_last_error())}"}]}')
	}
	return gql_response(200, '{"data":{"torDestroyHiddenService":{"destroyed":true,"onionAddress":"${esc(onion)}","remainingServices":0}}}')
}

fn resolve_tor_resolve(query string) http.Response {
	hostname := extract_arg(query, 'hostname')
	if hostname.len == 0 {
		return gql_response(200, '{"errors":[{"message":"hostname required"}]}')
	}
	if overlay_ffi_available {
		mut buf := [256]u8{}
		mut buf_len := usize(256)
		rc := C.echidna_tor_resolve(hostname.str, usize(hostname.len), &buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			return gql_response(200, '{"data":{"torResolve":{"hostname":"${esc(hostname)}","resolved":"${unsafe { tos(&buf[0], int(buf_len)) }}","via":"tor-socks5"}}}')
		}
		return gql_response(200, '{"errors":[{"message":"${esc(overlay_last_error())}"}]}')
	}
	return gql_response(200, '{"data":{"torResolve":{"hostname":"${esc(hostname)}","resolved":"198.51.100.42","via":"tor-socks5"}}}')
}

// ============================================================================
// Mutation Resolvers — IPFS
// ============================================================================

fn resolve_ipfs_connect(data string) http.Response {
	config := if data.len > 0 { data } else { '{"api_port":5001}' }
	if overlay_ffi_available {
		rc := C.echidna_ipfs_connect(config.str, usize(config.len))
		if rc == 0 {
			return gql_response(200, '{"data":{"ipfsConnect":{"connected":true,"network":"ipfs","apiPort":5001,"gatewayPort":8080}}}')
		}
		return gql_response(200, '{"errors":[{"message":"${esc(overlay_last_error())}"}]}')
	}
	return gql_response(200, '{"data":{"ipfsConnect":{"connected":true,"network":"ipfs","apiPort":5001,"gatewayPort":8080}}}')
}

fn resolve_ipfs_disconnect() http.Response {
	if overlay_ffi_available {
		C.echidna_ipfs_disconnect()
	}
	return gql_response(200, '{"data":{"ipfsDisconnect":{"disconnected":true,"network":"ipfs"}}}')
}

fn resolve_ipfs_add(query string) http.Response {
	data := extract_arg(query, 'data')
	if data.len == 0 {
		return gql_response(200, '{"errors":[{"message":"data required for ipfsAdd"}]}')
	}
	if overlay_ffi_available {
		mut cid_buf := [256]u8{}
		mut cid_len := usize(256)
		rc := C.echidna_ipfs_add(data.str, usize(data.len), &cid_buf[0], &cid_len)
		if rc == 0 && cid_len > 0 {
			cid := unsafe { tos(&cid_buf[0], int(cid_len)) }
			return gql_response(200, '{"data":{"ipfsAdd":{"added":true,"cid":"${esc(cid)}","size":${data.len}}}}')
		}
		return gql_response(200, '{"errors":[{"message":"${esc(overlay_last_error())}"}]}')
	}
	return gql_response(200, '{"data":{"ipfsAdd":{"added":true,"cid":"bafkreihdwdcefgh4dqkjv67uzcmw7ojee6xedzdetojuzjevtenrqpc","size":${data.len}}}}')
}

fn resolve_ipfs_cat(query string) http.Response {
	cid := extract_arg(query, 'cid')
	if cid.len == 0 {
		return gql_response(200, '{"errors":[{"message":"cid required"}]}')
	}
	if overlay_ffi_available {
		mut buf := [65536]u8{}
		mut buf_len := usize(65536)
		rc := C.echidna_ipfs_cat(cid.str, usize(cid.len), &buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			content := unsafe { tos(&buf[0], int(buf_len)) }
			return gql_response(200, '{"data":{"ipfsCat":{"cid":"${esc(cid)}","content":"${esc(content)}","size":${buf_len}}}}')
		}
		return gql_response(200, '{"errors":[{"message":"${esc(overlay_last_error())}"}]}')
	}
	return gql_response(200, '{"data":{"ipfsCat":{"cid":"${esc(cid)}","content":"(* ECHIDNA proof certificate *)","size":31}}}')
}

fn resolve_ipfs_pin(query string) http.Response {
	cid := extract_arg(query, 'cid')
	if cid.len == 0 {
		return gql_response(200, '{"errors":[{"message":"cid required"}]}')
	}
	if overlay_ffi_available {
		rc := C.echidna_ipfs_pin(cid.str, usize(cid.len))
		if rc == 0 {
			return gql_response(200, '{"data":{"ipfsPin":{"pinned":true,"cid":"${esc(cid)}","totalPinned":${C.echidna_ipfs_pin_count()}}}}')
		}
		return gql_response(200, '{"errors":[{"message":"${esc(overlay_last_error())}"}]}')
	}
	return gql_response(200, '{"data":{"ipfsPin":{"pinned":true,"cid":"${esc(cid)}","totalPinned":1}}}')
}

fn resolve_ipfs_unpin(query string) http.Response {
	cid := extract_arg(query, 'cid')
	if cid.len == 0 {
		return gql_response(200, '{"errors":[{"message":"cid required"}]}')
	}
	if overlay_ffi_available {
		rc := C.echidna_ipfs_unpin(cid.str, usize(cid.len))
		if rc == 0 {
			return gql_response(200, '{"data":{"ipfsUnpin":{"unpinned":true,"cid":"${esc(cid)}","totalPinned":${C.echidna_ipfs_pin_count()}}}}')
		}
		return gql_response(200, '{"errors":[{"message":"${esc(overlay_last_error())}"}]}')
	}
	return gql_response(200, '{"data":{"ipfsUnpin":{"unpinned":true,"cid":"${esc(cid)}","totalPinned":0}}}')
}

fn resolve_ipfs_dag_get(query string) http.Response {
	cid := extract_arg(query, 'cid')
	if cid.len == 0 {
		return gql_response(200, '{"errors":[{"message":"cid required"}]}')
	}
	if overlay_ffi_available {
		mut buf := [8192]u8{}
		mut buf_len := usize(8192)
		rc := C.echidna_ipfs_dag_get(cid.str, usize(cid.len), &buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			return gql_response(200, '{"data":{"ipfsDagGet":${unsafe { tos(&buf[0], int(buf_len)) }}}}')
		}
		return gql_response(200, '{"errors":[{"message":"${esc(overlay_last_error())}"}]}')
	}
	return gql_response(200, '{"data":{"ipfsDagGet":{"cid":"${esc(cid)}","links":0,"size":256,"dataSize":128}}}')
}

// ============================================================================
// Mutation Resolvers — Ethereum (stubbed)
// ============================================================================

fn resolve_eth_connect(data string) http.Response {
	config := if data.len > 0 { data } else { '{"rpc_url":"http://localhost:8545"}' }
	if overlay_ffi_available {
		rc := C.echidna_eth_connect(config.str, usize(config.len))
		if rc == 0 {
			return gql_response(200, '{"data":{"ethConnect":{"connected":true,"network":"ethereum","note":"Stubbed — Aerie future use"}}}')
		}
		return gql_response(200, '{"errors":[{"message":"${esc(overlay_last_error())}"}]}')
	}
	return gql_response(200, '{"data":{"ethConnect":{"connected":true,"network":"ethereum","note":"Stubbed — Aerie future use"}}}')
}

fn resolve_eth_disconnect() http.Response {
	if overlay_ffi_available {
		C.echidna_eth_disconnect()
	}
	return gql_response(200, '{"data":{"ethDisconnect":{"disconnected":true,"network":"ethereum"}}}')
}

fn resolve_eth_timestamp(query string) http.Response {
	proof_hash := extract_arg(query, 'proofHash')
	if proof_hash.len == 0 {
		return gql_response(200, '{"errors":[{"message":"proofHash required"}]}')
	}
	if overlay_ffi_available {
		mut buf := [2048]u8{}
		mut buf_len := usize(2048)
		rc := C.echidna_eth_timestamp_proof(proof_hash.str, usize(proof_hash.len), &buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			return gql_response(200, '{"data":{"ethTimestampProof":${unsafe { tos(&buf[0], int(buf_len)) }}}}')
		}
		return gql_response(200, '{"errors":[{"message":"${esc(overlay_last_error())}"}]}')
	}
	return gql_response(200, '{"data":{"ethTimestampProof":{"txHash":"0xdeadbeef...","blockNumber":19000000,"timestamp":${time.now().unix()},"proofHash":"${esc(proof_hash)}","status":"STUBBED"}}}')
}

fn resolve_eth_verify(query string) http.Response {
	tx_hash := extract_arg(query, 'txHash')
	if tx_hash.len == 0 {
		return gql_response(200, '{"errors":[{"message":"txHash required"}]}')
	}
	if overlay_ffi_available {
		mut buf := [2048]u8{}
		mut buf_len := usize(2048)
		rc := C.echidna_eth_verify_timestamp(tx_hash.str, usize(tx_hash.len), &buf[0], &buf_len)
		if rc == 0 && buf_len > 0 {
			return gql_response(200, '{"data":{"ethVerifyTimestamp":${unsafe { tos(&buf[0], int(buf_len)) }}}}')
		}
		return gql_response(200, '{"errors":[{"message":"${esc(overlay_last_error())}"}]}')
	}
	return gql_response(200, '{"data":{"ethVerifyTimestamp":{"verified":true,"txHash":"${esc(tx_hash)}","proofHash":"sha3-256:stub","blockNumber":19000000,"timestamp":${time.now().unix()},"status":"STUBBED"}}}')
}

// ============================================================================
// GraphiQL Playground
// ============================================================================

fn serve_graphiql() http.Response {
	html := '<!DOCTYPE html><html><head><title>ECHIDNA Overlay GraphQL</title>
<link rel="stylesheet" href="https://unpkg.com/graphiql/graphiql.min.css" />
<script crossorigin src="https://unpkg.com/react/umd/react.production.min.js"></script>
<script crossorigin src="https://unpkg.com/react-dom/umd/react-dom.production.min.js"></script>
<script crossorigin src="https://unpkg.com/graphiql/graphiql.min.js"></script>
</head><body style="margin:0"><div id="graphiql" style="height:100vh"></div>
<script>
const fetcher = GraphiQL.createFetcher({url: "/graphql"});
ReactDOM.render(React.createElement(GraphiQL, {fetcher, defaultQuery: "{ overlayHealth { healthy tor ipfs ethereum version ffiMode } }"}), document.getElementById("graphiql"));
</script></body></html>'
	mut header := http.new_header(key: .content_type, value: 'text/html; charset=utf-8')
	return http.new_response(
		status: .ok
		header: header
		body: html
	)
}

// --- Helpers ---

fn esc(s string) string {
	return s.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n').replace('\t', '\\t')
}

fn extract_arg(query string, key string) string {
	// Match GraphQL argument syntax: key: "value" or key: \"value\"
	patterns := ['${key}: "', '${key}:\\"', '${key}: \\"']
	for pattern in patterns {
		idx := query.index(pattern) or { continue }
		start := idx + pattern.len
		rest := query[start..]
		end := rest.index_any('"\\"') or { continue }
		if end > 0 {
			return rest[..end]
		}
	}
	return ''
}

fn extract_int_arg(query string, key string) int {
	patterns := ['${key}: ', '${key}:']
	for pattern in patterns {
		idx := query.index(pattern) or { continue }
		start := idx + pattern.len
		rest := query[start..].trim_space()
		mut end := 0
		for i, c in rest {
			if c >= `0` && c <= `9` {
				end = i + 1
			} else if end > 0 {
				break
			}
		}
		if end > 0 {
			return rest[..end].int()
		}
	}
	return 0
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
