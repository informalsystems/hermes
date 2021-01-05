//! ICS 03: IBC Connection implementation

pub mod connection;
/// Context definitions (dependencies for the protocol).
pub mod context;
pub mod events;
/// Message processing logic (protocol) for ICS 03.
pub mod handler;
pub mod msgs;
pub mod version;

mod error;
pub use error::Kind;
// todo: rename Kind into Error