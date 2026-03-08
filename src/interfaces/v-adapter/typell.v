// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// ECHIDNA TypeLL REST API Gateway — Port 7800
//
// Exposes TypeLL type-level computation operations via REST:
//
//   GET  /api/v1/health              — TypeLL server health
//   GET  /api/v1/status              — connection status
//   GET  /api/v1/version             — TypeLL version
//   POST /api/v1/connect             — connect to TypeLL server
//   POST /api/v1/disconnect          — disconnect from TypeLL
//   POST /api/v1/check               — type-check an expression
//   POST /api/v1/infer               — infer the type of an expression
//   POST /api/v1/refine              — apply refinement types
//   POST /api/v1/compute             — evaluate a type-level computation
//   GET  /api/v1/signatures          — list available type signatures
//   GET  /api/v1/universes           — get type universe hierarchy
//
// Links against libechidna_typell.so (Zig FFI layer) when available.
// Falls back to stub responses with X-TypeLL-Mode: stub header when FFI is absent.

module main

import net.http
import time

// --- Zig FFI extern declarations (libechidna_typell.so) ---

#flag -L @VMODROOT/../../ffi/zig/zig-out/lib
#flag -lechidna_typell

fn C.echidna_typell_connect(config_ptr &u8, config_len usize) int
fn C.echidna_typell_disconnect()
fn C.echidna_typell_status() int
fn C.echidna_typell_health(out_ptr &u8, out_len &usize) int
fn C.echidna_typell_check(expr_ptr &u8, expr_len usize, ctx_ptr &u8, ctx_len usize, out_ptr &u8, out_len &usize) int
fn C.echidna_typell_infer(expr_ptr &u8, expr_len usize, out_ptr &u8, out_len &usize) int
fn C.echidna_typell_refine(spec_ptr &u8, spec_len usize, cons_ptr &u8, cons_len usize, out_ptr &u8, out_len &usize) int
fn C.echidna_typell_compute(term_ptr &u8, term_len usize, out_ptr &u8, out_len &usize) int
fn C.echidna_typell_list_signatures(out_ptr &u8, out_len &usize) int
fn C.echidna_typell_universes(out_ptr &u8, out_len &usize) int
fn C.echidna_typell_version() &u8
fn C.echidna_typell_last_error() &u8

// --- FFI availability detection ---

mut ffi_available := false

fn init_typell_ffi() {
	unsafe {
		ver := C.echidna_typell_version()
		if ver != nil {
			ffi_available = true
		}
	}
}

// --- Response helpers ---

fn typell_response(mut res http.Response, status int, body string) {
	res.set_status(http.Status.from_int(status))
	res.header.set(.content_type, 'application/json')
	if ffi_available {
		res.header.set_custom('X-TypeLL-Mode', 'live') or {}
	} else {
		res.header.set_custom('X-TypeLL-Mode', 'stub') or {}
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
	return ''
}

// --- Request handler ---

struct TypeLLHandler {}

fn (mut handler TypeLLHandler) handle(req http.Request) http.Response {
	mut res := http.Response{
		header: http.new_header_from_map({
			http.CommonHeader.content_type: 'application/json'
		})
	}

	path := req.url.trim_right('/')

	match true {
		path == '/api/v1/health' {
			if ffi_available {
				result := ffi_buf_call(C.echidna_typell_health)
				if result.len > 0 {
					typell_response(mut res, 200, result)
				} else {
					typell_response(mut res, 503, '{"status":"error","message":"TypeLL health check failed"}')
				}
			} else {
				typell_response(mut res, 200, '{"status":"ok","version":"0.1.0","universes":4,"mode":"stub"}')
			}
		}
		path == '/api/v1/status' {
			if ffi_available {
				status := C.echidna_typell_status()
				status_name := match status {
					0 { 'disconnected' }
					1 { 'connecting' }
					2 { 'connected' }
					else { 'error' }
				}
				typell_response(mut res, 200, '{"status":"${status_name}","status_code":${status}}')
			} else {
				typell_response(mut res, 200, '{"status":"stub","status_code":0}')
			}
		}
		path == '/api/v1/version' {
			if ffi_available {
				unsafe {
					ver := C.echidna_typell_version()
					if ver != nil {
						typell_response(mut res, 200, '{"version":"${cstring_to_vstring(ver)}"}')
					} else {
						typell_response(mut res, 200, '{"version":"unknown"}')
					}
				}
			} else {
				typell_response(mut res, 200, '{"version":"0.1.0","mode":"stub"}')
			}
		}
		path == '/api/v1/connect' && req.method == .post {
			if ffi_available {
				config := req.data
				if config.len > 0 {
					rc := C.echidna_typell_connect(config.str, usize(config.len))
					if rc == 0 {
						typell_response(mut res, 200, '{"connected":true}')
					} else {
						typell_response(mut res, 500, '{"connected":false,"error_code":${rc}}')
					}
				} else {
					typell_response(mut res, 400, '{"error":"Empty configuration"}')
				}
			} else {
				typell_response(mut res, 200, '{"connected":true,"mode":"stub"}')
			}
		}
		path == '/api/v1/disconnect' && req.method == .post {
			if ffi_available {
				C.echidna_typell_disconnect()
			}
			typell_response(mut res, 200, '{"disconnected":true}')
		}
		path == '/api/v1/check' && req.method == .post {
			body := req.data
			if ffi_available && body.len > 0 {
				ctx := '{}'
				mut out_buf := [65536]u8{}
				mut out_len := usize(65536)
				rc := C.echidna_typell_check(body.str, usize(body.len), ctx.str, usize(ctx.len), &out_buf[0], &out_len)
				if rc == 0 && out_len > 0 {
					unsafe { typell_response(mut res, 200, tos(&out_buf[0], int(out_len))) }
				} else {
					typell_response(mut res, 422, '{"error":"Type check failed","error_code":${rc}}')
				}
			} else {
				typell_response(mut res, 200, '{"well_typed":true,"type":"Nat -> Nat","mode":"stub"}')
			}
		}
		path == '/api/v1/infer' && req.method == .post {
			body := req.data
			if ffi_available && body.len > 0 {
				mut out_buf := [65536]u8{}
				mut out_len := usize(65536)
				rc := C.echidna_typell_infer(body.str, usize(body.len), &out_buf[0], &out_len)
				if rc == 0 && out_len > 0 {
					unsafe { typell_response(mut res, 200, tos(&out_buf[0], int(out_len))) }
				} else {
					typell_response(mut res, 422, '{"error":"Type inference failed","error_code":${rc}}')
				}
			} else {
				typell_response(mut res, 200, '{"inferred_type":"Nat -> Nat","mode":"stub"}')
			}
		}
		path == '/api/v1/refine' && req.method == .post {
			body := req.data
			if ffi_available && body.len > 0 {
				cons := '[]'
				mut out_buf := [65536]u8{}
				mut out_len := usize(65536)
				rc := C.echidna_typell_refine(body.str, usize(body.len), cons.str, usize(cons.len), &out_buf[0], &out_len)
				if rc == 0 && out_len > 0 {
					unsafe { typell_response(mut res, 200, tos(&out_buf[0], int(out_len))) }
				} else {
					typell_response(mut res, 422, '{"error":"Refinement failed","error_code":${rc}}')
				}
			} else {
				typell_response(mut res, 200, '{"refined_type":"{n : Nat | n > 0}","mode":"stub"}')
			}
		}
		path == '/api/v1/compute' && req.method == .post {
			body := req.data
			if ffi_available && body.len > 0 {
				mut out_buf := [65536]u8{}
				mut out_len := usize(65536)
				rc := C.echidna_typell_compute(body.str, usize(body.len), &out_buf[0], &out_len)
				if rc == 0 && out_len > 0 {
					unsafe { typell_response(mut res, 200, tos(&out_buf[0], int(out_len))) }
				} else {
					typell_response(mut res, 422, '{"error":"Computation failed","error_code":${rc}}')
				}
			} else {
				typell_response(mut res, 200, '{"result":"S (S (S Z))","type":"Nat","mode":"stub"}')
			}
		}
		path == '/api/v1/signatures' {
			if ffi_available {
				result := ffi_buf_call(C.echidna_typell_list_signatures)
				if result.len > 0 {
					typell_response(mut res, 200, result)
				} else {
					typell_response(mut res, 500, '{"error":"Failed to list signatures"}')
				}
			} else {
				typell_response(mut res, 200, '[{"name":"id","type":"forall A, A -> A"}]')
			}
		}
		path == '/api/v1/universes' {
			if ffi_available {
				result := ffi_buf_call(C.echidna_typell_universes)
				if result.len > 0 {
					typell_response(mut res, 200, result)
				} else {
					typell_response(mut res, 500, '{"error":"Failed to get universes"}')
				}
			} else {
				typell_response(mut res, 200, '{"levels":["Type","Type1","Type2","Typeω"],"mode":"stub"}')
			}
		}
		else {
			typell_response(mut res, 404, '{"error":"Not found","path":"${path}"}')
		}
	}

	return res
}

fn main() {
	init_typell_ffi()
	mode := if ffi_available { 'live (libechidna_typell.so loaded)' } else { 'stub' }
	eprintln('ECHIDNA TypeLL REST adapter starting on :7800 [${mode}]')

	mut handler := TypeLLHandler{}
	mut server := http.Server{
		handler: handler
		addr: ':7800'
	}
	server.listen_and_serve()
}
