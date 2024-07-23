//! Definitions of domain types used in the ICS-08 Wasm light client implementation.

pub mod client_message;
pub mod client_state;
pub mod consensus_state;
pub mod error;
pub mod proto;

pub const WASM_CLIENT_TYPE: &str = "08-wasm";
