//! ICS 04: Channel implementation that facilitates communication between
//! applications and the chains those applications are built upon.

pub mod channel;
pub mod context;
pub mod error;

pub mod packet;

pub mod commitment;
mod version;
pub use version::Version;
