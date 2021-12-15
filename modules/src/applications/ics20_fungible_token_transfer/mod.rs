//! ICS 20: Token Transfer implementation allows for multi-chain denomination handling, which
//! constitutes a "fungible token transfer bridge module" between the IBC routing module and an
//! asset tracking module.
pub mod context;
pub mod error;
pub mod msgs;
pub mod relay_application_logic;

mod denom;
pub use denom::*;

/// The port identifier that the ICS20 applications
/// typically bind with.
pub const PORT_ID: &str = "transfer";

/// ICS20 application current version.
pub const VERSION: &str = "ics20-1";
