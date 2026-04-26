# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# src/julia/ipc.jl
#
# Cap'n Proto IPC client stub — L1 wave 1 deliverable.
#
# Replaces the HTTP+JSON Rust↔Julia hot path on the GNN ranking endpoint
# with Cap'n Proto framing over a Unix domain socket (primary) or TCP
# fallback. Transport selection mirrors the Rust side in
# src/rust/ipc/mod.rs: check $ECHIDNA_IPC_SOCK first, then UDS default,
# then TCP via $ECHIDNA_IPC_HOST / $ECHIDNA_IPC_PORT.
#
# Status: STUB — connect_ipc opens the socket; gnn_rank_request throws
# until the Cap'n Proto serialisation layer lands (see TODO block below).
#
# Wire protocol: schemas/echidna.capnp, schema ID @0xd3b45f8ae1c79012.
# Versioning rules: schemas/VERSIONING.md.

# ─── TODO: what must land before this stub becomes real ──────────────────────
#
# DECISION (2026-04-26): Use CapnProto.jl (Option A).
#
# Implementation steps:
#   1. Add CapnProto to Project.toml / Manifest.toml.
#   2. Add a Julia codegen target to the `just capnp-gen` Justfile recipe
#      so that `capnp compile -ojulia schemas/echidna.capnp` generates
#      GnnRankRequest / GnnRankResponse Julia structs.
#   3. Replace gnn_rank_request body with:
#        msg = CapnProto.build(GnnRankRequest, parse_request_fields(request_json))
#        write(sock.sock, CapnProto.encode(msg))
#        raw = read(sock.sock, CapnProto.ResponseHeader)
#        return CapnProto.decode(GnnRankResponse, raw)
#   4. If CapnProto.jl's RPC layer is missing/broken, patch upstream rather
#      than switching approaches. The Zig C-ABI shim in
#      ffi/zig/src/capnp_bridge.zig remains as a fallback of last resort.
#
# Gated on: L3 Tier-1 green for ≥ 7 days (same gate as Rust IPC side).
# ─────────────────────────────────────────────────────────────────────────────

module EchidnaIPC

using Sockets

# ─── Constants ────────────────────────────────────────────────────────────────

"Default Unix domain socket path (matches Rust DEFAULT_SOCK_PATH)."
const DEFAULT_SOCK_PATH = "/run/echidna/ipc.sock"

"Default TCP fallback port (matches Rust DEFAULT_TCP_PORT)."
const DEFAULT_TCP_PORT = 9090

# ─── Transport struct ─────────────────────────────────────────────────────────

"""
    CapnpSocket

Holds an open (or pending) IPC connection to the ECHIDNA Rust core.

Fields:
- `sock` — the open socket (`TCPSocket` for TCP; `nothing` when UDS is the
           chosen path but the Julia stdlib UDS API is not yet wired).
- `path` — the socket path / host:port string, used for logging and
           reconnect diagnostics.

Use `connect_ipc()` to construct a connected instance.
"""
mutable struct CapnpSocket
    sock::Union{Nothing, Sockets.TCPSocket}
    path::String
end

# ─── Transport helpers ────────────────────────────────────────────────────────

"Resolve the Unix domain socket path from the environment."
function _ipc_sock_path()::String
    get(ENV, "ECHIDNA_IPC_SOCK", DEFAULT_SOCK_PATH)
end

"Resolve the TCP fallback host and port from the environment."
function _tcp_host_port()::Tuple{String,Int}
    host = get(ENV, "ECHIDNA_IPC_HOST", "127.0.0.1")
    port = parse(Int, get(ENV, "ECHIDNA_IPC_PORT", string(DEFAULT_TCP_PORT)))
    (host, port)
end

# ─── Connection ───────────────────────────────────────────────────────────────

"""
    connect_ipc(; path = _ipc_sock_path()) -> CapnpSocket

Open an IPC connection to the ECHIDNA Rust core.

Transport selection (mirrors `Transport::from_env` in src/rust/ipc/mod.rs):
1. Unix domain socket at `path` — primary, lowest latency.
2. TCP fallback at `\$ECHIDNA_IPC_HOST`:`\$ECHIDNA_IPC_PORT` (default
   127.0.0.1:9090) — used when the UDS socket file does not exist.

Throws an `ErrorException` if neither transport is reachable.  Callers
that need graceful degradation should catch and fall back to the HTTP
endpoint (`src/julia/api/gnn_endpoint.jl`).

# Examples
```julia
sock = connect_ipc()
sock = connect_ipc(path = "/tmp/test.sock")
```
"""
function connect_ipc(; path::String = _ipc_sock_path())::CapnpSocket
    if ispath(path)
        # UDS socket file present.  The real UDS connection (via Zig shim or
        # CapnProto.jl) is deferred to L1 wave 1; record the path so the
        # stub can report useful diagnostics.
        @info "IPC: UDS socket found at $path (transport deferred to L1 wave 1)"
        return CapnpSocket(nothing, path)
    end

    # TCP fallback — mirrors Rust Transport::Tcp branch.
    host, port = _tcp_host_port()
    @info "IPC: UDS path '$path' not found, attempting TCP fallback $host:$port"
    try
        tcp_sock = Sockets.connect(host, port)
        return CapnpSocket(tcp_sock, "$host:$port")
    catch e
        error(
            "IPC connection failed: UDS path '$path' not found and TCP " *
            "$host:$port refused ($e). Is the ECHIDNA Rust core running?"
        )
    end
end

"""
    close_ipc(sock::CapnpSocket)

Close the IPC connection if open.  Safe to call on a not-yet-connected stub.
"""
function close_ipc(sock::CapnpSocket)
    if !isnothing(sock.sock)
        try
            close(sock.sock)
        catch e
            @warn "IPC close error (ignored)" exception=e
        end
        sock.sock = nothing
    end
end

# ─── Request / response ───────────────────────────────────────────────────────

"""
    gnn_rank_request(sock, request_json) -> String

Send a GNN rank request to the Rust core and return the JSON response.

**L1 wave 1 stub**: always throws until the Cap'n Proto serialisation layer
(CapnProto.jl or Zig C-ABI shim) is wired in.  Callers should catch
`ErrorException` and fall back to the HTTP endpoint.

When implemented the protocol will be:
1. Deserialise `request_json` into a `GnnRankRequest` Cap'n Proto message.
2. Write the framed Cap'n Proto bytes to `sock.sock`.
3. Read a framed `GnnRankResponse` message back.
4. Return the response as JSON (for compatibility with existing HTTP callers).

See the TODO block at the top of this file for Options A and B.

# Arguments
- `sock`         — an open `CapnpSocket` from `connect_ipc()`.
- `request_json` — JSON string matching `GnnRankRequest` fields:
                   `requestId`, `graph`, `topK`, `minScore`,
                   `includeEmbeddings`, `numLayers`, `useAttention`.

# Returns
JSON string matching `GnnRankResponse`: `requestId`, `rankings`,
`embeddings`, `modelVersion`, `elapsedMs`.

# Throws
`ErrorException` — always, until L1 wave 1 is complete.
"""
function gnn_rank_request(sock::CapnpSocket, request_json::String)::String
    _ = sock
    _ = request_json
    error(
        "IPC not yet implemented: L1 wave 1 pending. " *
        "Use HTTP fallback at http://127.0.0.1:8090/gnn/rank."
    )
end

# ─── Probe ────────────────────────────────────────────────────────────────────

"""
    ipc_available(; path = _ipc_sock_path()) -> Bool

Non-throwing reachability probe.  Returns `true` if the UDS socket file exists
or the TCP fallback accepts a connection within ~200 ms.

Mirrors `Transport::probe()` in src/rust/ipc/mod.rs.
"""
function ipc_available(; path::String = _ipc_sock_path())::Bool
    ispath(path) && return true
    host, port = _tcp_host_port()
    try
        s = Sockets.connect(host, port)
        close(s)
        return true
    catch
        return false
    end
end

end  # module EchidnaIPC
