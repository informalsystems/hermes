//! ICS 03: IBC Connection implementation

//pub mod connection;
// Use the generated proto file for the connection according to prost_build instructions
pub mod connection {
    include!(concat!(env!("OUT_DIR"), "/ibc.connection.rs"));
}
pub mod error;
pub mod events;
pub mod exported;
pub mod msgs;
pub mod query;
