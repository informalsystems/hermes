/// Stellar chain endpoint for the Hermes IBC relayer.
///
/// Stellar uses Federated Byzantine Agreement (SCP) for consensus and exposes a
/// JSON-RPC 2.0 HTTP interface (`stellar-rpc`). IBC logic runs as a Soroban smart
/// contract. There is no custom gateway service — the relayer talks directly to stellar-rpc.
///
/// Implementation follows the same pattern as the Cardano chain endpoint:
/// - Polling event source (no WebSocket push)
/// - Ed25519 key derivation (SEP-0005 / SLIP-0010, path `m/44'/148'/account'`)
/// - Non-Cosmos chain (`is_cosmos_compatibility_mode()` returns `false`)
///
/// ## Implementation status
/// - [x] PR 1 — IBC types in `ibc-relayer-types` (`ics10_stellar`)
/// - [x] PR 2 — Module scaffold: config, error, RPC client (this PR)
/// - [ ] PR 3 — Key management: keyring, signing key pair, signer
/// - [ ] PR 4 — `AnyClientState::Stellar`, `AnyConsensusState::Stellar`
/// - [ ] PR 5 — Event pipeline: parser + polling event source
/// - [ ] PR 6 — `ChainEndpoint` implementation (queries + bootstrap + spawn wiring)
/// - [ ] PR 7 — Transaction submission (`send_messages_and_wait_commit`)
/// - [ ] PR 8 — Cleanup, tests, documentation
pub mod config;
pub mod error;
pub mod rpc_client;

/// Placeholder for the full `ChainEndpoint` implementation (PR 6).
pub struct StellarChainEndpoint;

/// Type alias used by the relayer runtime.
pub type StellarChain = StellarChainEndpoint;
