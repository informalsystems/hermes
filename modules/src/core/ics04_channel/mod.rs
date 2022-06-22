//! ICS 04: Channel implementation that facilitates communication between
//! applications and the chains those applications are built upon.

pub mod channel;
pub mod context;
pub mod events;
pub mod handler;
pub mod msgs;
pub mod packet;

pub use ibc_base::ics04_channel::commitment;
pub use ibc_base::ics04_channel::error;
pub use ibc_base::ics04_channel::Version;
