//! The `all_for_one` trait exposes the concrete APIs that users use to
//! construct concrete relayer implementations. In other words, the public
//! API methods that are part of this trait are used to facilitate the
//! functionality of relayers.

pub mod birelay;
pub mod chain;
pub mod relay;
