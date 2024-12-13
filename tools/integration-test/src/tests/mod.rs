/*!
   All test cases are placed within this module.

   We expose the modules as public so that cargo doc
   will pick up the definition by default.
*/

pub mod clear_packet;
pub mod client_expiration;
pub mod client_filter;
pub mod client_refresh;
pub mod client_settings;
#[cfg(not(feature = "celestia"))]
pub mod client_upgrade;
pub mod connection_delay;
pub mod consensus_states;
#[cfg(not(feature = "no-denom-trace"))]
pub mod denom_trace;
pub mod error_events;
pub mod execute_schedule;
pub mod handshake_on_start;
pub mod ics20_filter;
pub mod memo;
pub mod python;
pub mod query_packet;
#[cfg(not(feature = "celestia"))]
pub mod sequence_filter;
pub mod supervisor;
pub mod tendermint;
#[cfg(not(feature = "celestia"))]
pub mod ternary_transfer;
pub mod transfer;

#[cfg(any(doc, feature = "async-icq"))]
pub mod async_icq;

#[cfg(any(doc, feature = "authz"))]
pub mod authz;

#[cfg(any(doc, feature = "channel-upgrade"))]
pub mod channel_upgrade;

#[cfg(any(doc, feature = "ics29-fee"))]
pub mod fee;

#[cfg(any(doc, feature = "ordered"))]
pub mod ordered_channel;

#[cfg(any(doc, feature = "ordered"))]
pub mod ordered_channel_clear;

#[cfg(any(doc, feature = "ica"))]
pub mod ica;

#[cfg(any(doc, feature = "manual"))]
pub mod manual;

#[cfg(any(doc, feature = "example"))]
pub mod example;

#[cfg(any(doc, feature = "forward-packet"))]
pub mod forward;

#[cfg(any(doc, feature = "ics31"))]
pub mod ics31;

#[cfg(any(doc, feature = "clean-workers"))]
pub mod clean_workers;

#[cfg(any(doc, feature = "fee-grant"))]
pub mod fee_grant;

#[cfg(any(doc, feature = "interchain-security"))]
pub mod interchain_security;

#[cfg(any(doc, feature = "dynamic-gas-fee"))]
pub mod dynamic_gas_fee;

#[cfg(any(doc, feature = "benchmark"))]
pub mod benchmark;
