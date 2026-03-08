// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// ECHIDNA Tentacles REST API Gateway — Port 8300
//
// Exposes 7-Tentacles agent operations via REST:
//
//   GET  /api/v1/health                  — tentacles system health
//   GET  /api/v1/version                 — tentacles version
//   POST /api/v1/init                    — initialise agent system
//   POST /api/v1/shutdown                — shut down agent system
//   GET  /api/v1/agents                  — list all 7 agents with status
//   GET  /api/v1/agents/:id/status       — agent status
//   GET  /api/v1/agents/:id/phase        — agent OODA phase
//   GET  /api/v1/agents/:id/stage        — agent reveal stage
//   POST /api/v1/agents/:id/task         — dispatch task to agent
//   POST /api/v1/agents/:id/cancel       — cancel agent task
//   GET  /api/v1/stage                   — get global stage
//   PUT  /api/v1/stage                   — set global stage
//   GET  /api/v1/events                  — poll agent events (JSON array)
//   POST /api/v1/broadcast               — broadcast from an agent
//
// Links against libechidna_tentacles.so (Zig FFI layer) when available.
// Falls back to stub responses with X-Tentacles-Mode: stub header when FFI is absent.

module main

import net.http
import time

// --- Zig FFI extern declarations (libechidna_tentacles.so) ---

#flag -L @VMODROOT/../../ffi/zig/zig-out/lib
#flag -lechidna_tentacles

fn C.echidna_tentacles_init() int
fn C.echidna_tentacles_shutdown()
fn C.echidna_tentacles_agent_status(agent_id int) int
fn C.echidna_tentacles_agent_phase(agent_id int) int
fn C.echidna_tentacles_agent_stage(agent_id int) int
fn C.echidna_tentacles_dispatch_task(agent_id int, task_ptr &u8, task_len usize) int
fn C.echidna_tentacles_cancel_task(agent_id int) int
fn C.echidna_tentacles_set_global_stage(stage_id int) int
fn C.echidna_tentacles_get_global_stage() int
fn C.echidna_tentacles_poll_events(out_ptr &u8, out_len &usize) int
fn C.echidna_tentacles_event_count() int
fn C.echidna_tentacles_broadcast(source_id int, payload_ptr &u8, payload_len usize) int
fn C.echidna_tentacles_version() &u8
fn C.echidna_tentacles_last_error() &u8
fn C.echidna_tentacles_agent_count() int

// Callback registration
fn C.echidna_tentacles_register_on_phase_change(cb fn (int, int, int)) int
fn C.echidna_tentacles_register_on_task_complete(cb fn (int, int)) int
fn C.echidna_tentacles_register_on_error(cb fn (int, int, &u8, usize)) int

// --- FFI availability detection ---

mut ffi_available := false

fn init_tentacles_ffi() {
	unsafe {
		ver := C.echidna_tentacles_version()
		if ver != nil {
			ffi_available = true
			// Register event callbacks
			C.echidna_tentacles_register_on_phase_change(on_phase_change)
			C.echidna_tentacles_register_on_task_complete(on_task_complete)
			C.echidna_tentacles_register_on_error(on_tentacles_error)
		}
	}
}

// --- Event buffer ---

struct TentaclesEvent {
	kind       string
	agent_id   int
	detail     string
	timestamp  i64
}

mut event_buffer := []TentaclesEvent{}
const max_events = 1000

fn push_tentacles_event(kind string, agent_id int, detail string) {
	if event_buffer.len >= max_events {
		event_buffer.delete(0)
	}
	event_buffer << TentaclesEvent{
		kind: kind
		agent_id: agent_id
		detail: detail
		timestamp: time.now().unix()
	}
}

// --- Callback handlers ---

fn on_phase_change(agent_id int, old_phase int, new_phase int) {
	push_tentacles_event('phase_change', agent_id, '${old_phase}->${new_phase}')
}

fn on_task_complete(agent_id int, result_code int) {
	push_tentacles_event('task_complete', agent_id, 'rc=${result_code}')
}

fn on_tentacles_error(agent_id int, error_code int, msg_ptr &u8, msg_len usize) {
	msg := unsafe { tos(msg_ptr, int(msg_len)) }
	push_tentacles_event('error', agent_id, 'code=${error_code}: ${msg}')
}

// --- Agent name helper ---

fn agent_name(id int) string {
	return match id {
		0 { 'Red (Parser)' }
		1 { 'Orange (Concurrency)' }
		2 { 'Yellow (Type System)' }
		3 { 'Green (AST Architect)' }
		4 { 'Blue (Auditor)' }
		5 { 'Indigo (Metaprogrammer)' }
		6 { 'Violet (Governance)' }
		else { 'Unknown' }
	}
}

fn stage_name(id int) string {
	return match id {
		0 { 'Cuttle' }
		1 { 'Squidlet' }
		2 { 'Duet' }
		3 { 'Octopus' }
		else { 'Unknown' }
	}
}

fn phase_name(id int) string {
	return match id {
		0 { 'Observe' }
		1 { 'Orient' }
		2 { 'Decide' }
		3 { 'Act' }
		else { 'Unknown' }
	}
}

fn status_name(id int) string {
	return match id {
		0 { 'idle' }
		1 { 'busy' }
		2 { 'error' }
		3 { 'disabled' }
		else { 'unknown' }
	}
}

// --- Response helpers ---

fn tentacles_response(mut res http.Response, status int, body string) {
	res.set_status(http.Status.from_int(status))
	res.header.set(.content_type, 'application/json')
	if ffi_available {
		res.header.set_custom('X-Tentacles-Mode', 'live') or {}
	} else {
		res.header.set_custom('X-Tentacles-Mode', 'stub') or {}
	}
	res.body = body
}

fn ffi_buf_call(f fn (&u8, &usize) int) string {
	mut buf := [65536]u8{}
	mut buf_len := usize(65536)
	rc := f(&buf[0], &buf_len)
	if rc == 0 && buf_len > 0 {
		unsafe { return tos(&buf[0], int(buf_len)) }
	}
	return '{"error":"ffi call failed","code":${rc}}'
}

// --- Route handlers ---

fn handle_health(mut res http.Response) {
	if ffi_available {
		ver := unsafe { cstring_to_vstring(C.echidna_tentacles_version()) }
		count := C.echidna_tentacles_agent_count()
		active := C.echidna_tentacles_event_count()
		tentacles_response(mut res, 200, '{"status":"ok","version":"${ver}","agentCount":${count},"activeAgents":${active}}')
	} else {
		tentacles_response(mut res, 200, '{"status":"stub","version":"stub","agentCount":7,"activeAgents":0}')
	}
}

fn handle_version(mut res http.Response) {
	if ffi_available {
		ver := unsafe { cstring_to_vstring(C.echidna_tentacles_version()) }
		tentacles_response(mut res, 200, '{"version":"${ver}"}')
	} else {
		tentacles_response(mut res, 200, '{"version":"stub"}')
	}
}

fn handle_init(mut res http.Response) {
	if ffi_available {
		rc := C.echidna_tentacles_init()
		if rc == 0 {
			tentacles_response(mut res, 200, '{"status":"initialised"}')
		} else {
			tentacles_response(mut res, 500, '{"error":"init failed","code":${rc}}')
		}
	} else {
		tentacles_response(mut res, 200, '{"status":"stub_initialised"}')
	}
}

fn handle_shutdown(mut res http.Response) {
	if ffi_available {
		C.echidna_tentacles_shutdown()
	}
	tentacles_response(mut res, 200, '{"status":"shutdown"}')
}

fn handle_agents(mut res http.Response) {
	if ffi_available {
		json := ffi_buf_call(C.echidna_tentacles_poll_events)
		tentacles_response(mut res, 200, json)
	} else {
		mut agents := '['
		for i in 0 .. 7 {
			if i > 0 { agents += ',' }
			agents += '{"id":${i},"name":"${agent_name(i)}","status":"idle","phase":"observe","stage":"cuttle"}'
		}
		agents += ']'
		tentacles_response(mut res, 200, agents)
	}
}

fn handle_agent_status(agent_id int, mut res http.Response) {
	if ffi_available {
		status := C.echidna_tentacles_agent_status(agent_id)
		if status < 0 {
			tentacles_response(mut res, 400, '{"error":"invalid agent","code":${status}}')
		} else {
			tentacles_response(mut res, 200, '{"id":${agent_id},"name":"${agent_name(agent_id)}","status":"${status_name(status)}"}')
		}
	} else {
		tentacles_response(mut res, 200, '{"id":${agent_id},"name":"${agent_name(agent_id)}","status":"idle"}')
	}
}

fn handle_agent_phase(agent_id int, mut res http.Response) {
	if ffi_available {
		phase := C.echidna_tentacles_agent_phase(agent_id)
		if phase < 0 {
			tentacles_response(mut res, 400, '{"error":"invalid agent","code":${phase}}')
		} else {
			tentacles_response(mut res, 200, '{"id":${agent_id},"phase":"${phase_name(phase)}"}')
		}
	} else {
		tentacles_response(mut res, 200, '{"id":${agent_id},"phase":"observe"}')
	}
}

fn handle_dispatch_task(agent_id int, body string, mut res http.Response) {
	if ffi_available {
		rc := unsafe { C.echidna_tentacles_dispatch_task(agent_id, body.str, usize(body.len)) }
		if rc == 0 {
			tentacles_response(mut res, 200, '{"status":"dispatched","agent":${agent_id}}')
		} else {
			tentacles_response(mut res, 400, '{"error":"dispatch failed","code":${rc}}')
		}
	} else {
		tentacles_response(mut res, 200, '{"status":"stub_dispatched","agent":${agent_id}}')
	}
}

fn handle_cancel_task(agent_id int, mut res http.Response) {
	if ffi_available {
		rc := C.echidna_tentacles_cancel_task(agent_id)
		if rc == 0 {
			tentacles_response(mut res, 200, '{"status":"cancelled","agent":${agent_id}}')
		} else {
			tentacles_response(mut res, 400, '{"error":"cancel failed","code":${rc}}')
		}
	} else {
		tentacles_response(mut res, 200, '{"status":"stub_cancelled","agent":${agent_id}}')
	}
}

fn handle_get_stage(mut res http.Response) {
	if ffi_available {
		stage := C.echidna_tentacles_get_global_stage()
		tentacles_response(mut res, 200, '{"stage":"${stage_name(stage)}","stageId":${stage}}')
	} else {
		tentacles_response(mut res, 200, '{"stage":"cuttle","stageId":0}')
	}
}

fn handle_set_stage(body string, mut res http.Response) {
	// Expect body like {"stageId": 2}
	stage_id := body.find_between('"stageId":', '}').trim_space().int()
	if ffi_available {
		rc := C.echidna_tentacles_set_global_stage(stage_id)
		if rc == 0 {
			tentacles_response(mut res, 200, '{"status":"stage_set","stage":"${stage_name(stage_id)}"}')
		} else {
			tentacles_response(mut res, 400, '{"error":"invalid stage","code":${rc}}')
		}
	} else {
		tentacles_response(mut res, 200, '{"status":"stub_stage_set","stage":"${stage_name(stage_id)}"}')
	}
}

fn handle_events(mut res http.Response) {
	mut json := '['
	for i, evt in event_buffer {
		if i > 0 { json += ',' }
		json += '{"kind":"${evt.kind}","agentId":${evt.agent_id},"detail":"${evt.detail}","timestamp":${evt.timestamp}}'
	}
	json += ']'
	tentacles_response(mut res, 200, json)
}

fn handle_broadcast(body string, mut res http.Response) {
	// Expect body like {"sourceId": 0, "payload": "..."}
	source_id := body.find_between('"sourceId":', ',').trim_space().int()
	if ffi_available {
		rc := unsafe { C.echidna_tentacles_broadcast(source_id, body.str, usize(body.len)) }
		if rc == 0 {
			tentacles_response(mut res, 200, '{"status":"broadcast_sent","source":${source_id}}')
		} else {
			tentacles_response(mut res, 400, '{"error":"broadcast failed","code":${rc}}')
		}
	} else {
		push_tentacles_event('broadcast', source_id, body)
		tentacles_response(mut res, 200, '{"status":"stub_broadcast","source":${source_id}}')
	}
}

// --- Main server ---

fn main() {
	init_tentacles_ffi()

	mut server := http.Server.init(.{
		.addr = ':8300'
		.handler = fn (req http.Request, mut res http.Response) {
			path := req.url.path
			method := req.method

			// CORS headers
			res.header.set(.access_control_allow_origin, '*')
			res.header.set(.access_control_allow_methods, 'GET, POST, PUT, OPTIONS')
			res.header.set(.access_control_allow_headers, 'Content-Type')

			if method == .options {
				res.set_status(.no_content)
				return
			}

			match true {
				path == '/api/v1/health' && method == .get {
					handle_health(mut res)
				}
				path == '/api/v1/version' && method == .get {
					handle_version(mut res)
				}
				path == '/api/v1/init' && method == .post {
					handle_init(mut res)
				}
				path == '/api/v1/shutdown' && method == .post {
					handle_shutdown(mut res)
				}
				path == '/api/v1/agents' && method == .get {
					handle_agents(mut res)
				}
				path == '/api/v1/stage' && method == .get {
					handle_get_stage(mut res)
				}
				path == '/api/v1/stage' && method == .put {
					handle_set_stage(req.body, mut res)
				}
				path == '/api/v1/events' && method == .get {
					handle_events(mut res)
				}
				path == '/api/v1/broadcast' && method == .post {
					handle_broadcast(req.body, mut res)
				}
				path.starts_with('/api/v1/agents/') {
					parts := path.split('/')
					if parts.len >= 5 {
						agent_id := parts[4].int()
						if parts.len >= 6 {
							match parts[5] {
								'status' { handle_agent_status(agent_id, mut res) }
								'phase' { handle_agent_phase(agent_id, mut res) }
								'task' { handle_dispatch_task(agent_id, req.body, mut res) }
								'cancel' { handle_cancel_task(agent_id, mut res) }
								else { tentacles_response(mut res, 404, '{"error":"unknown endpoint"}') }
							}
						} else {
							handle_agent_status(agent_id, mut res)
						}
					} else {
						tentacles_response(mut res, 400, '{"error":"missing agent id"}')
					}
				}
				else {
					tentacles_response(mut res, 404, '{"error":"not found","path":"${path}"}')
				}
			}
		}
	})

	println('ECHIDNA Tentacles REST adapter listening on :8300')
	server.listen_and_serve()
}
