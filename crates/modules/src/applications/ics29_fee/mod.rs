//! The implementation of the ICS 29 fee payment [spec](https://github.com/cosmos/ibc/blob/main/spec/app/ics-029-fee-payment/README.md).
//! Enables an incentivization layer for relayers such that relayer operators are rewarded
//! for successfully relaying packets.
//!
//! The documentation for this module makes use of some terminology, which is defined below:
//! 1. Forward relayer: The relayer that submits the `recv_packet` message for a given packet.
//! 2. Reverse relayer: The relayer that submits the `ack_packet` message for a given packet.
//! 3. Timeout relayer: The relayer that submits the `timeout_packet` message for a given packet.

pub mod error;
pub mod events;
pub mod msgs;
pub mod packet_fee;
