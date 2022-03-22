//! ibc-proto library gives the developer access to the Cosmos SDK IBC proto-defined structs.

// Todo: automate the creation of this module setup based on the dots in the filenames.
// This module setup is necessary because the generated code contains "super::" calls for dependencies.

#![cfg_attr(not(feature = "std"), no_std)]
#![deny(warnings, trivial_casts, trivial_numeric_casts, unused_import_braces)]
#![allow(clippy::large_enum_variant)]
#![allow(rustdoc::bare_urls)]
#![forbid(unsafe_code)]
#![doc(html_root_url = "https://docs.rs/ibc-proto/0.16.0")]

extern crate alloc;

#[cfg(not(feature = "std"))]
#[macro_use]
extern crate core as std;

macro_rules! include_proto {
    ($path:literal) => {
        include!(concat!("prost/", $path));
    };
}

/// The version (commit hash) of the Cosmos SDK used when generating this library.
pub const COSMOS_SDK_COMMIT: &str = include_str!("COSMOS_SDK_COMMIT");

/// The version (commit hash) of IBC Go used when generating this library.
pub const IBC_GO_COMMIT: &str = include_str!("IBC_GO_COMMIT");

pub mod google {
    pub mod protobuf {
        include_proto!("google.protobuf.rs");

        // source: https://github.com/tokio-rs/prost/blob/master/prost-types/src/lib.rs
        use core::convert::TryFrom;
        use core::i32;
        use core::i64;
        use core::time;

        // The Protobuf `Duration` and `Timestamp` types can't delegate to the standard library equivalents
        // because the Protobuf versions are signed. To make them easier to work with, `From` conversions
        // are defined in both directions.

        const NANOS_PER_SECOND: i32 = 1_000_000_000;
        const NANOS_MAX: i32 = NANOS_PER_SECOND - 1;

        impl Duration {
            /// Normalizes the duration to a canonical format.
            ///
            /// Based on [`google::protobuf::util::CreateNormalized`][1].
            /// [1]: https://github.com/google/protobuf/blob/v3.3.2/src/google/protobuf/util/time_util.cc#L79-L100
            pub fn normalize(&mut self) {
                // Make sure nanos is in the range.
                if self.nanos <= -NANOS_PER_SECOND || self.nanos >= NANOS_PER_SECOND {
                    if let Some(seconds) = self
                        .seconds
                        .checked_add((self.nanos / NANOS_PER_SECOND) as i64)
                    {
                        self.seconds = seconds;
                        self.nanos %= NANOS_PER_SECOND;
                    } else if self.nanos < 0 {
                        // Negative overflow! Set to the least normal value.
                        self.seconds = i64::MIN;
                        self.nanos = -NANOS_MAX;
                    } else {
                        // Positive overflow! Set to the greatest normal value.
                        self.seconds = i64::MAX;
                        self.nanos = NANOS_MAX;
                    }
                }

                // nanos should have the same sign as seconds.
                if self.seconds < 0 && self.nanos > 0 {
                    if let Some(seconds) = self.seconds.checked_add(1) {
                        self.seconds = seconds;
                        self.nanos -= NANOS_PER_SECOND;
                    } else {
                        // Positive overflow! Set to the greatest normal value.
                        debug_assert_eq!(self.seconds, i64::MAX);
                        self.nanos = NANOS_MAX;
                    }
                } else if self.seconds > 0 && self.nanos < 0 {
                    if let Some(seconds) = self.seconds.checked_sub(1) {
                        self.seconds = seconds;
                        self.nanos += NANOS_PER_SECOND;
                    } else {
                        // Negative overflow! Set to the least normal value.
                        debug_assert_eq!(self.seconds, i64::MIN);
                        self.nanos = -NANOS_MAX;
                    }
                }
                // TODO: should this be checked?
                // debug_assert!(self.seconds >= -315_576_000_000 && self.seconds <= 315_576_000_000,
                //               "invalid duration: {:?}", self);
            }
        }

        /// Converts a `std::time::Duration` to a `Duration`.
        impl From<time::Duration> for Duration {
            fn from(duration: time::Duration) -> Duration {
                let seconds = duration.as_secs();
                let seconds = if seconds > i64::MAX as u64 {
                    i64::MAX
                } else {
                    seconds as i64
                };
                let nanos = duration.subsec_nanos();
                let nanos = if nanos > i32::MAX as u32 {
                    i32::MAX
                } else {
                    nanos as i32
                };
                let mut duration = Duration { seconds, nanos };
                duration.normalize();
                duration
            }
        }

        impl TryFrom<Duration> for time::Duration {
            type Error = time::Duration;

            /// Converts a `Duration` to a result containing a positive (`Ok`) or negative (`Err`)
            /// `std::time::Duration`.
            fn try_from(mut duration: Duration) -> Result<time::Duration, time::Duration> {
                duration.normalize();
                if duration.seconds >= 0 {
                    Ok(time::Duration::new(
                        duration.seconds as u64,
                        duration.nanos as u32,
                    ))
                } else {
                    Err(time::Duration::new(
                        (-duration.seconds) as u64,
                        (-duration.nanos) as u32,
                    ))
                }
            }
        }

        impl Timestamp {
            /// Normalizes the timestamp to a canonical format.
            ///
            /// Based on [`google::protobuf::util::CreateNormalized`][1].
            /// [1]: https://github.com/google/protobuf/blob/v3.3.2/src/google/protobuf/util/time_util.cc#L59-L77
            #[cfg(feature = "std")]
            pub fn normalize(&mut self) {
                // Make sure nanos is in the range.
                if self.nanos <= -NANOS_PER_SECOND || self.nanos >= NANOS_PER_SECOND {
                    if let Some(seconds) = self
                        .seconds
                        .checked_add((self.nanos / NANOS_PER_SECOND) as i64)
                    {
                        self.seconds = seconds;
                        self.nanos %= NANOS_PER_SECOND;
                    } else if self.nanos < 0 {
                        // Negative overflow! Set to the earliest normal value.
                        self.seconds = i64::MIN;
                        self.nanos = 0;
                    } else {
                        // Positive overflow! Set to the latest normal value.
                        self.seconds = i64::MAX;
                        self.nanos = 999_999_999;
                    }
                }

                // For Timestamp nanos should be in the range [0, 999999999].
                if self.nanos < 0 {
                    if let Some(seconds) = self.seconds.checked_sub(1) {
                        self.seconds = seconds;
                        self.nanos += NANOS_PER_SECOND;
                    } else {
                        // Negative overflow! Set to the earliest normal value.
                        debug_assert_eq!(self.seconds, i64::MIN);
                        self.nanos = 0;
                    }
                }
            }
        }

        /// Implements the unstable/naive version of `Eq`: a basic equality check on the internal fields of the `Timestamp`.
        /// This implies that `normalized_ts != non_normalized_ts` even if `normalized_ts == non_normalized_ts.normalized()`.
        #[cfg(feature = "std")]
        impl Eq for Timestamp {}

        #[cfg(feature = "std")]
        #[allow(clippy::derive_hash_xor_eq)] // Derived logic is correct: comparing the 2 fields for equality
        impl std::hash::Hash for Timestamp {
            fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                self.seconds.hash(state);
                self.nanos.hash(state);
            }
        }

        #[cfg(feature = "std")]
        impl From<std::time::SystemTime> for Timestamp {
            fn from(system_time: std::time::SystemTime) -> Timestamp {
                let (seconds, nanos) = match system_time.duration_since(std::time::UNIX_EPOCH) {
                    Ok(duration) => {
                        let seconds = i64::try_from(duration.as_secs()).unwrap();
                        (seconds, duration.subsec_nanos() as i32)
                    }
                    Err(error) => {
                        let duration = error.duration();
                        let seconds = i64::try_from(duration.as_secs()).unwrap();
                        let nanos = duration.subsec_nanos() as i32;
                        if nanos == 0 {
                            (-seconds, 0)
                        } else {
                            (-seconds - 1, 1_000_000_000 - nanos)
                        }
                    }
                };
                Timestamp { seconds, nanos }
            }
        }

        /// Indicates that a [`Timestamp`] could not be converted to
        /// [`SystemTime`][std::time::SystemTime] because it is out of range.
        ///
        /// The range of times that can be represented by `SystemTime` depends on the platform.
        /// All `Timestamp`s are likely representable on 64-bit Unix-like platforms, but
        /// other platforms, such as Windows and 32-bit Linux, may not be able to represent
        /// the full range of `Timestamp`s.
        #[cfg(feature = "std")]
        #[derive(Debug)]
        #[non_exhaustive]
        pub struct TimestampOutOfSystemRangeError {
            pub timestamp: Timestamp,
        }

        #[cfg(feature = "std")]
        impl core::fmt::Display for TimestampOutOfSystemRangeError {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                write!(
                    f,
                    "{:?} is not representable as a `SystemTime` because it is out of range",
                    self
                )
            }
        }

        #[cfg(feature = "std")]
        impl std::error::Error for TimestampOutOfSystemRangeError {}

        #[cfg(feature = "std")]
        impl TryFrom<Timestamp> for std::time::SystemTime {
            type Error = TimestampOutOfSystemRangeError;

            fn try_from(mut timestamp: Timestamp) -> Result<std::time::SystemTime, Self::Error> {
                let orig_timestamp = timestamp.clone();
                timestamp.normalize();

                let system_time = if timestamp.seconds >= 0 {
                    std::time::UNIX_EPOCH
                        .checked_add(time::Duration::from_secs(timestamp.seconds as u64))
                } else {
                    std::time::UNIX_EPOCH
                        .checked_sub(time::Duration::from_secs((-timestamp.seconds) as u64))
                };

                let system_time = system_time.and_then(|system_time| {
                    system_time.checked_add(time::Duration::from_nanos(timestamp.nanos as u64))
                });

                system_time.ok_or(TimestampOutOfSystemRangeError {
                    timestamp: orig_timestamp,
                })
            }
        }
    }
}

pub mod cosmos {
    pub mod auth {
        pub mod v1beta1 {
            include_proto!("cosmos.auth.v1beta1.rs");
            /// EthAccount defines an Ethermint account.
            /// TODO: remove when/if a canonical `EthAccount`
            /// lands in the next Cosmos SDK release
            /// (note https://github.com/cosmos/cosmos-sdk/pull/9981
            /// only adds the PubKey type)
            #[derive(Clone, PartialEq, ::prost::Message)]
            pub struct EthAccount {
                #[prost(message, optional, tag = "1")]
                pub base_account: ::core::option::Option<BaseAccount>,
                #[prost(bytes = "vec", tag = "2")]
                pub code_hash: ::prost::alloc::vec::Vec<u8>,
            }
        }
    }
    pub mod staking {
        pub mod v1beta1 {
            include_proto!("cosmos.staking.v1beta1.rs");
        }
    }
    pub mod base {
        pub mod abci {
            pub mod v1beta1 {
                include_proto!("cosmos.base.abci.v1beta1.rs");
            }
        }
        pub mod kv {
            pub mod v1beta1 {
                include_proto!("cosmos.base.kv.v1beta1.rs");
            }
        }
        pub mod query {
            pub mod v1beta1 {
                include_proto!("cosmos.base.query.v1beta1.rs");
            }

            pub mod pagination {
                use super::v1beta1::PageRequest;

                pub fn all() -> Option<PageRequest> {
                    Some(PageRequest {
                        limit: u64::MAX,
                        ..Default::default()
                    })
                }
            }
        }
        pub mod reflection {
            pub mod v1beta1 {
                include_proto!("cosmos.base.reflection.v1beta1.rs");
            }
        }
        pub mod store {
            pub mod v1beta1 {
                include_proto!("cosmos.base.store.v1beta1.rs");
            }
        }
        pub mod v1beta1 {
            include_proto!("cosmos.base.v1beta1.rs");
        }
        pub mod tendermint {
            pub mod v1beta1 {
                include_proto!("cosmos.base.tendermint.v1beta1.rs");
            }
        }
    }
    pub mod crypto {
        pub mod multisig {
            pub mod v1beta1 {
                include_proto!("cosmos.crypto.multisig.v1beta1.rs");
            }
        }
    }
    pub mod tx {
        pub mod signing {
            pub mod v1beta1 {
                include_proto!("cosmos.tx.signing.v1beta1.rs");
            }
        }
        pub mod v1beta1 {
            include_proto!("cosmos.tx.v1beta1.rs");
        }
    }
    pub mod upgrade {
        pub mod v1beta1 {
            include_proto!("cosmos.upgrade.v1beta1.rs");
        }
    }
    pub mod gov {
        pub mod v1beta1 {
            include_proto!("cosmos.gov.v1beta1.rs");
        }
    }
}

pub mod ibc {
    #[deprecated(since = "0.15.0", note = "Use `ibc_proto::ibc::applications` instead")]
    pub mod apps {
        pub use super::applications::*;
    }
    pub mod applications {
        pub mod transfer {
            pub mod v1 {
                include_proto!("ibc.applications.transfer.v1.rs");
            }
        }
        pub mod interchain_accounts {
            pub mod v1 {
                include_proto!("ibc.applications.interchain_accounts.v1.rs");
            }
            pub mod controller {
                pub mod v1 {
                    include_proto!("ibc.applications.interchain_accounts.controller.v1.rs");
                }
            }
            pub mod host {
                pub mod v1 {
                    include_proto!("ibc.applications.interchain_accounts.host.v1.rs");
                }
            }
        }
    }
    pub mod core {
        pub mod channel {
            pub mod v1 {
                include_proto!("ibc.core.channel.v1.rs");
            }
        }
        pub mod client {
            pub mod v1 {
                include_proto!("ibc.core.client.v1.rs");
            }
        }
        pub mod commitment {
            pub mod v1 {
                include_proto!("ibc.core.commitment.v1.rs");
            }
        }
        pub mod connection {
            pub mod v1 {
                include_proto!("ibc.core.connection.v1.rs");
            }
        }
        pub mod types {
            pub mod v1 {
                include_proto!("ibc.core.types.v1.rs");
            }
        }
    }
    pub mod lightclients {
        pub mod localhost {
            pub mod v1 {
                include_proto!("ibc.lightclients.localhost.v1.rs");
            }
        }
        pub mod solomachine {
            pub mod v1 {
                include_proto!("ibc.lightclients.solomachine.v1.rs");
            }
        }
        pub mod tendermint {
            pub mod v1 {
                include_proto!("ibc.lightclients.tendermint.v1.rs");
            }
        }
    }
    pub mod mock {
        include_proto!("ibc.mock.rs");
    }
}

pub mod ics23 {
    include_proto!("ics23.rs");
}

pub(crate) mod base64 {
    use alloc::string::String;
    use alloc::vec::Vec;

    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(v: &[u8], serializer: S) -> Result<S::Ok, S::Error> {
        let mut buf = String::new();
        base64::encode_config_buf(v, base64::STANDARD, &mut buf);

        String::serialize(&buf, serializer)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<Vec<u8>, D::Error> {
        let base64 = String::deserialize(deserializer)?;

        let mut buf = Vec::new();
        base64::decode_config_buf(base64.as_bytes(), base64::STANDARD, &mut buf)
            .map_err(serde::de::Error::custom)?;

        Ok(buf)
    }
}
