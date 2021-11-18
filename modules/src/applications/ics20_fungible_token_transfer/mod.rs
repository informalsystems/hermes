//! ICS 20: IBC Transfer implementation
pub mod context;
pub mod error;
pub mod msgs;
pub mod relay_application_logic;

/// The port identifier that the ICS20 applications
/// typically bind with.
pub const PORT_ID: &str = "transfer";

/// ICS20 application current version.
pub const VERSION: &str = "ics20-1";
