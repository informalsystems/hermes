/*!
   All test cases are placed within this module.

   We expose the modules as public so that cargo doc
   will pick up the definition by default.
*/

#[cfg(not(feature = "namada"))]
pub mod clear_packet;
#[cfg(not(feature = "namada"))]
pub mod client_expiration;
#[cfg(not(feature = "namada"))]
pub mod client_filter;
pub mod client_refresh;
#[cfg(not(feature = "namada"))]
pub mod client_settings;
#[cfg(not(any(feature = "celestia", feature = "juno", feature = "namada")))]
pub mod client_upgrade;
pub mod connection_delay;
#[cfg(not(feature = "namada"))]
pub mod consensus_states;
#[cfg(not(feature = "namada"))]
pub mod denom_trace;
#[cfg(not(feature = "namada"))]
pub mod error_events;
pub mod execute_schedule;
pub mod handshake_on_start;
pub mod ics20_filter;
#[cfg(not(feature = "namada"))]
pub mod memo;
#[cfg(not(feature = "namada"))]
pub mod python;
pub mod query_packet;
#[cfg(not(feature = "namada"))]
pub mod supervisor;
#[cfg(not(feature = "namada"))]
pub mod tendermint;
#[cfg(not(any(feature = "celestia", feature = "namada")))]
pub mod ternary_transfer;
pub mod transfer;

#[cfg(any(doc, feature = "async-icq"))]
pub mod async_icq;

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
