// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// ECHIDNA BoJ Client REST API Gateway — Port 7700
//
// Exposes BoJ cartridge management operations via REST:
//
//   GET  /api/v1/health              — BoJ server health
//   GET  /api/v1/status              — connection status
//   GET  /api/v1/version             — BoJ version
//   POST /api/v1/connect             — connect to BoJ server
//   POST /api/v1/disconnect          — disconnect from BoJ
//   GET  /api/v1/cartridges          — list all cartridges
//   GET  /api/v1/cartridges/:name    — get cartridge details
//   POST /api/v1/cartridges/:name/load   — load (mount) cartridge
//   POST /api/v1/cartridges/:name/unload — unload (unmount) cartridge
//   POST /api/v1/cartridges/:name/invoke — invoke a cartridge tool
//   GET  /api/v1/topology            — get service topology matrix
//   GET  /api/v1/umoja/status        — Umoja federation status
//
// Links against libechidna_boj.so (Zig FFI layer) when available.
// Falls back to stub responses with X-Boj-Mode: stub header when FFI is absent.

module main

import net.http
import time

// --- Zig FFI extern declarations (libechidna_boj.so) ---

#flag -L @VMODROOT/../../ffi/zig/zig-out/lib
#flag -lechidna_boj

fn C.echidna_boj_connect(config_ptr &u8, config_len usize) int
fn C.echidna_boj_disconnect()
fn C.echidna_boj_status() int
fn C.echidna_boj_health(out_ptr &u8, out_len &usize) int
fn C.echidna_boj_list_cartridges(out_ptr &u8, out_len &usize) int
fn C.echidna_boj_get_cartridge(name_ptr &u8, name_len usize, out_ptr &u8, out_len &usize) int
fn C.echidna_boj_load_cartridge(name_ptr &u8, name_len usize) int
fn C.echidna_boj_unload_cartridge(name_ptr &u8, name_len usize) int
fn C.echidna_boj_invoke(name_ptr &u8, name_len usize, tool_ptr &u8, tool_len usize, args_ptr &u8, args_len usize, out_ptr &u8, out_len &usize) int
fn C.echidna_boj_topology(out_ptr &u8, out_len &usize) int
fn C.echidna_boj_umoja_status(out_ptr &u8, out_len &usize) int
fn C.echidna_boj_cartridge_count() int
fn C.echidna_boj_version() &u8
fn C.echidna_boj_last_error() &u8

// --- FFI availability detection ---

mut ffi_available := false

fn init_boj_ffi() {
	unsafe {
		ver := C.echidna_boj_version()
		if ver != nil {
			ffi_available = true
		}
	}
}

// --- Response helpers ---

fn boj_response(mut res http.Response, status int, body string) {
	res.set_status(http.Status.from_int(status))
	res.header.set(.content_type, 'application/json')
	if ffi_available {
		res.header.set_custom('X-Boj-Mode', 'live') or {}
	} else {
		res.header.set_custom('X-Boj-Mode', 'stub') or {}
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

struct BojHandler {}

struct BojServer {
	port int = 7700
}

fn (mut handler BojHandler) handle(req http.Request) http.Response {
	mut res := http.Response{
		header: http.new_header_from_map({
			http.CommonHeader.content_type: 'application/json'
		})
	}

	path := req.url.trim_right('/')

	match true {
		path == '/api/v1/health' {
			if ffi_available {
				result := ffi_buf_call(C.echidna_boj_health)
				if result.len > 0 {
					boj_response(mut res, 200, result)
				} else {
					boj_response(mut res, 503, '{"status":"error","message":"BoJ health check failed"}')
				}
			} else {
				boj_response(mut res, 200, '{"status":"ok","version":"0.2.0","cartridges":14,"mode":"stub"}')
			}
		}
		path == '/api/v1/status' {
			if ffi_available {
				status := C.echidna_boj_status()
				status_name := match status {
					0 { 'disconnected' }
					1 { 'connecting' }
					2 { 'connected' }
					else { 'error' }
				}
				boj_response(mut res, 200, '{"status":"${status_name}","status_code":${status}}')
			} else {
				boj_response(mut res, 200, '{"status":"stub","status_code":0}')
			}
		}
		path == '/api/v1/version' {
			if ffi_available {
				unsafe {
					ver := C.echidna_boj_version()
					if ver != nil {
						boj_response(mut res, 200, '{"version":"${cstring_to_vstring(ver)}"}')
					} else {
						boj_response(mut res, 200, '{"version":"unknown"}')
					}
				}
			} else {
				boj_response(mut res, 200, '{"version":"0.2.0","mode":"stub"}')
			}
		}
		path == '/api/v1/connect' && req.method == .post {
			if ffi_available {
				config := req.data
				if config.len > 0 {
					rc := C.echidna_boj_connect(config.str, usize(config.len))
					if rc == 0 {
						boj_response(mut res, 200, '{"connected":true}')
					} else {
						boj_response(mut res, 500, '{"connected":false,"error_code":${rc}}')
					}
				} else {
					boj_response(mut res, 400, '{"error":"Empty configuration"}')
				}
			} else {
				boj_response(mut res, 200, '{"connected":true,"mode":"stub"}')
			}
		}
		path == '/api/v1/disconnect' && req.method == .post {
			if ffi_available {
				C.echidna_boj_disconnect()
			}
			boj_response(mut res, 200, '{"disconnected":true}')
		}
		path == '/api/v1/cartridges' && req.method == .get {
			if ffi_available {
				result := ffi_buf_call(C.echidna_boj_list_cartridges)
				if result.len > 0 {
					boj_response(mut res, 200, result)
				} else {
					boj_response(mut res, 500, '{"error":"Failed to list cartridges"}')
				}
			} else {
				boj_response(mut res, 200, '[{"name":"proof-mcp","status":"Ready","domain":"Proof","mounted":false}]')
			}
		}
		path == '/api/v1/topology' {
			if ffi_available {
				result := ffi_buf_call(C.echidna_boj_topology)
				if result.len > 0 {
					boj_response(mut res, 200, result)
				} else {
					boj_response(mut res, 500, '{"error":"Failed to get topology"}')
				}
			} else {
				boj_response(mut res, 200, '{"protocols":9,"domains":14,"cartridges":14,"mode":"stub"}')
			}
		}
		path == '/api/v1/umoja/status' {
			if ffi_available {
				result := ffi_buf_call(C.echidna_boj_umoja_status)
				if result.len > 0 {
					boj_response(mut res, 200, result)
				} else {
					boj_response(mut res, 500, '{"error":"Failed to get Umoja status"}')
				}
			} else {
				boj_response(mut res, 200, '{"federation":"idle","peers":0,"mode":"stub"}')
			}
		}
		else {
			// Cartridge-specific routes: /api/v1/cartridges/:name/...
			if path.starts_with('/api/v1/cartridges/') {
				parts := path.replace('/api/v1/cartridges/', '').split('/')
				if parts.len >= 1 {
					name := parts[0]
					if parts.len == 1 {
						// GET /cartridges/:name
						if ffi_available {
							mut buf := [65536]u8{}
							mut buf_len := usize(65536)
							rc := C.echidna_boj_get_cartridge(name.str, usize(name.len), &buf[0], &buf_len)
							if rc == 0 && buf_len > 0 {
								unsafe { boj_response(mut res, 200, tos(&buf[0], int(buf_len))) }
							} else {
								boj_response(mut res, 404, '{"error":"Cartridge not found","name":"${name}"}')
							}
						} else {
							boj_response(mut res, 200, '{"name":"${name}","status":"Ready","mode":"stub"}')
						}
					} else if parts.len == 2 {
						action := parts[1]
						match action {
							'load' {
								if ffi_available {
									rc := C.echidna_boj_load_cartridge(name.str, usize(name.len))
									if rc == 0 {
										boj_response(mut res, 200, '{"loaded":true,"name":"${name}"}')
									} else {
										boj_response(mut res, 500, '{"loaded":false,"error_code":${rc}}')
									}
								} else {
									boj_response(mut res, 200, '{"loaded":true,"name":"${name}","mode":"stub"}')
								}
							}
							'unload' {
								if ffi_available {
									rc := C.echidna_boj_unload_cartridge(name.str, usize(name.len))
									if rc == 0 {
										boj_response(mut res, 200, '{"unloaded":true,"name":"${name}"}')
									} else {
										boj_response(mut res, 500, '{"unloaded":false,"error_code":${rc}}')
									}
								} else {
									boj_response(mut res, 200, '{"unloaded":true,"name":"${name}","mode":"stub"}')
								}
							}
							'invoke' {
								if ffi_available {
									body := req.data
									// Parse tool and args from JSON body
									// Simplified: pass raw body as args
									tool := 'default'
									mut out_buf := [65536]u8{}
									mut out_len := usize(65536)
									rc := C.echidna_boj_invoke(name.str, usize(name.len), tool.str, usize(tool.len), body.str, usize(body.len), &out_buf[0], &out_len)
									if rc == 0 && out_len > 0 {
										unsafe { boj_response(mut res, 200, tos(&out_buf[0], int(out_len))) }
									} else {
										boj_response(mut res, 500, '{"error":"Invoke failed","error_code":${rc}}')
									}
								} else {
									boj_response(mut res, 200, '{"status":"ok","result":{},"mode":"stub"}')
								}
							}
							else {
								boj_response(mut res, 404, '{"error":"Unknown action","action":"${action}"}')
							}
						}
					}
				}
			} else {
				boj_response(mut res, 404, '{"error":"Not found","path":"${path}"}')
			}
		}
	}

	return res
}

fn main() {
	init_boj_ffi()
	mode := if ffi_available { 'live (libechidna_boj.so loaded)' } else { 'stub' }
	eprintln('ECHIDNA BoJ REST adapter starting on :7700 [${mode}]')

	mut handler := BojHandler{}
	mut server := http.Server{
		handler: handler
		addr: ':7700'
	}
	server.listen_and_serve()
}
