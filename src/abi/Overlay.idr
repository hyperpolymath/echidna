-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- ECHIDNA Overlay Network ABI — Tor, IPFS, Ethereum
--
-- Defines type-safe interfaces for overlay/decentralised network components:
--   - Tor: Hidden service management, circuit control, SOCKS5 proxy
--   - IPFS: Content-addressed storage, pinning, DAG traversal
--   - Ethereum: Proof certificate timestamping (stubbed for Aerie)
--
-- All types are C-ABI compatible (repr(C) equivalent) for FFI bridging.
-- Zero believe_me. All proofs constructive.

module Overlay

import Data.Vect

%default total

-- ============================================================================
-- Overlay Network Kind
-- ============================================================================

||| Which overlay network a handle targets.
public export
data OverlayKind = Tor | IPFS | Ethereum

||| C-ABI encoding for OverlayKind.
public export
overlayKindToInt : OverlayKind -> Int
overlayKindToInt Tor      = 0
overlayKindToInt IPFS     = 1
overlayKindToInt Ethereum = 2

||| Inverse mapping (partial — returns Maybe).
public export
overlayKindFromInt : Int -> Maybe OverlayKind
overlayKindFromInt 0 = Just Tor
overlayKindFromInt 1 = Just IPFS
overlayKindFromInt 2 = Just Ethereum
overlayKindFromInt _ = Nothing

||| Round-trip proof: encoding then decoding yields the original kind.
public export
overlayKindRoundTrip : (k : OverlayKind) -> overlayKindFromInt (overlayKindToInt k) = Just k
overlayKindRoundTrip Tor      = Refl
overlayKindRoundTrip IPFS     = Refl
overlayKindRoundTrip Ethereum = Refl

-- ============================================================================
-- Tor Types
-- ============================================================================

||| Tor circuit status.
public export
data TorCircuitStatus = CircuitBuilding | CircuitBuilt | CircuitClosed | CircuitFailed

public export
torCircuitStatusToInt : TorCircuitStatus -> Int
torCircuitStatusToInt CircuitBuilding = 0
torCircuitStatusToInt CircuitBuilt    = 1
torCircuitStatusToInt CircuitClosed   = 2
torCircuitStatusToInt CircuitFailed   = 3

||| Tor hidden service descriptor.
public export
record TorHiddenService where
  constructor MkTorHiddenService
  onionAddress : String     -- .onion address (v3, 56 chars + .onion)
  port         : Int        -- Virtual port
  targetPort   : Int        -- Local target port
  isActive     : Bool

||| Tor control connection configuration.
public export
record TorControlConfig where
  constructor MkTorControlConfig
  controlHost : String      -- Default: "127.0.0.1"
  controlPort : Int         -- Default: 9051
  socksPort   : Int         -- Default: 9050
  authMethod  : Int         -- 0=none, 1=cookie, 2=password
  authData    : String      -- Cookie path or password

||| Tor circuit hop (for path analysis).
public export
record TorCircuitHop where
  constructor MkTorCircuitHop
  fingerprint : String      -- 40-char hex relay fingerprint
  nickname    : String      -- Relay nickname
  ipAddress   : String      -- IP address
  orPort      : Int         -- OR port
  isExit      : Bool        -- Whether this is an exit relay
  country     : String      -- 2-letter country code

-- ============================================================================
-- IPFS Types
-- ============================================================================

||| IPFS content identifier version.
public export
data CidVersion = CidV0 | CidV1

public export
cidVersionToInt : CidVersion -> Int
cidVersionToInt CidV0 = 0
cidVersionToInt CidV1 = 1

||| IPFS pin status.
public export
data PinStatus = Pinned | Unpinned | PinQueued | PinFailed

public export
pinStatusToInt : PinStatus -> Int
pinStatusToInt Pinned   = 0
pinStatusToInt Unpinned = 1
pinStatusToInt PinQueued = 2
pinStatusToInt PinFailed = 3

||| IPFS content descriptor.
public export
record IpfsContent where
  constructor MkIpfsContent
  cid         : String      -- Content identifier (CIDv0 or CIDv1)
  cidVersion  : CidVersion
  size        : Int         -- Content size in bytes
  contentType : String      -- MIME type
  pinned      : PinStatus

||| IPFS node configuration.
public export
record IpfsConfig where
  constructor MkIpfsConfig
  apiHost     : String      -- Default: "127.0.0.1"
  apiPort     : Int         -- Default: 5001
  gatewayPort : Int         -- Default: 8080
  repoPath    : String      -- IPFS repo path

||| IPFS DAG node for proof graph traversal.
public export
record IpfsDagNode where
  constructor MkIpfsDagNode
  cid       : String
  data_     : String        -- Raw data (base64-encoded for binary)
  linkCount : Int           -- Number of child links
  nodeSize  : Int           -- Total node size in bytes

-- ============================================================================
-- Ethereum Types (Stubbed — Aerie future use)
-- ============================================================================

||| Ethereum network target.
public export
data EthNetwork = EthMainnet | EthSepolia | EthHolesky | EthLocal

public export
ethNetworkToInt : EthNetwork -> Int
ethNetworkToInt EthMainnet = 0
ethNetworkToInt EthSepolia = 1
ethNetworkToInt EthHolesky = 2
ethNetworkToInt EthLocal   = 3

||| Ethereum proof timestamp record.
||| Used for anchoring proof certificates on-chain.
public export
record EthProofTimestamp where
  constructor MkEthProofTimestamp
  txHash        : String    -- Transaction hash (0x-prefixed, 66 chars)
  blockNumber   : Int       -- Block number
  timestamp     : Int       -- Unix timestamp
  proofHash     : String    -- SHA3-256 hash of the proof certificate
  contractAddr  : String    -- Timestamping contract address

||| Ethereum RPC configuration.
public export
record EthConfig where
  constructor MkEthConfig
  rpcUrl      : String      -- JSON-RPC endpoint
  network     : EthNetwork
  chainId     : Int         -- Chain ID (1=mainnet, 11155111=sepolia)

-- ============================================================================
-- Overlay Status (unified across all three)
-- ============================================================================

||| Connection/readiness status for any overlay network.
public export
data OverlayStatus
  = OverlayDisconnected
  | OverlayConnecting
  | OverlayConnected
  | OverlayError String

public export
overlayStatusToInt : OverlayStatus -> Int
overlayStatusToInt OverlayDisconnected = 0
overlayStatusToInt OverlayConnecting   = 1
overlayStatusToInt OverlayConnected    = 2
overlayStatusToInt (OverlayError _)    = 3

-- ============================================================================
-- FFI Function Signatures (what the Zig FFI must implement)
-- ============================================================================

-- C-ABI function signatures declared here, implemented in ffi/zig/src/overlay.zig.
-- Each function returns an Int status code (0 = success, negative = error).
--
-- Tor:
--   echidna_tor_connect(config_ptr, config_len) -> status
--   echidna_tor_disconnect() -> void
--   echidna_tor_create_hidden_service(port, target_port) -> status
--   echidna_tor_destroy_hidden_service(onion_ptr, onion_len) -> status
--   echidna_tor_get_circuit(circuit_id, out_ptr, out_len) -> status
--   echidna_tor_list_circuits(out_ptr, out_len) -> status
--   echidna_tor_resolve(hostname_ptr, hostname_len, out_ptr, out_len) -> status
--   echidna_tor_status() -> int (OverlayStatus ordinal)
--
-- IPFS:
--   echidna_ipfs_connect(config_ptr, config_len) -> status
--   echidna_ipfs_disconnect() -> void
--   echidna_ipfs_add(data_ptr, data_len, out_cid_ptr, out_cid_len) -> status
--   echidna_ipfs_cat(cid_ptr, cid_len, out_ptr, out_len) -> status
--   echidna_ipfs_pin(cid_ptr, cid_len) -> status
--   echidna_ipfs_unpin(cid_ptr, cid_len) -> status
--   echidna_ipfs_dag_get(cid_ptr, cid_len, out_ptr, out_len) -> status
--   echidna_ipfs_status() -> int (OverlayStatus ordinal)
--
-- Ethereum (stubbed):
--   echidna_eth_connect(config_ptr, config_len) -> status
--   echidna_eth_disconnect() -> void
--   echidna_eth_timestamp_proof(proof_hash_ptr, proof_hash_len, out_ptr, out_len) -> status
--   echidna_eth_verify_timestamp(tx_hash_ptr, tx_hash_len, out_ptr, out_len) -> status
--   echidna_eth_status() -> int (OverlayStatus ordinal)
