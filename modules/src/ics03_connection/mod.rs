//! ICS 03: IBC Connection implementation

pub mod connection;
pub mod error;
pub mod events;
pub mod exported;
pub mod msgs;
pub mod query;

// Use the generated proto file for the connection according to prost_build instructions
pub mod proto_ibc_connection {
    include!(concat!(env!("OUT_DIR"), "/ibc.connection.rs"));
}
