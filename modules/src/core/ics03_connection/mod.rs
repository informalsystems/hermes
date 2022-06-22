//! ICS 03: Connection implementation for connecting a client
//! on the local chain with a client on a remote chain.

/// Context definitions (dependencies for the protocol).
pub mod context;
pub mod events;
/// Message processing logic (protocol) for ICS 03.
pub mod handler;
pub mod msgs;

pub use ibc_base::ics03_connection::connection;
pub use ibc_base::ics03_connection::error;
pub use ibc_base::ics03_connection::version;
