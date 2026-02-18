//! Generated protobuf code for Cardano-specific gRPC services
//!
//! These files are checked in and should not be edited by hand.

// Allow clippy warnings for generated code
#![allow(clippy::all)]
#![allow(warnings)]

// Cosmos dependencies
pub mod cosmos_proto {
    include!("cosmos_proto.rs");
}

pub mod cosmos {
    pub mod base {
        pub mod query {
            pub mod v1beta1 {
                include!("cosmos.base.query.v1beta1.rs");
            }
        }
    }
    pub mod ics23 {
        pub mod v1 {
            include!("cosmos.ics23.v1.rs");
        }
    }
    pub mod upgrade {
        pub mod v1beta1 {
            include!("cosmos.upgrade.v1beta1.rs");
        }
    }
}

// The `google.api` proto includes documentation snippets that are not valid Rust code.
// Exclude it from doctest builds to keep `cargo test` (which runs doctests by default)
// working without disabling doctests for the whole crate.
#[cfg(not(doctest))]
pub mod google {
    pub mod api {
        include!("google.api.rs");
    }
}

// IBC core modules
pub mod ibc {
    pub mod cardano {
        pub mod v1 {
            include!("ibc.cardano.v1.rs");
        }
    }
    pub mod core {
        pub mod client {
            pub mod v1 {
                include!("ibc.core.client.v1.rs");
            }
        }
        pub mod connection {
            pub mod v1 {
                include!("ibc.core.connection.v1.rs");
            }
        }
        pub mod channel {
            pub mod v1 {
                include!("ibc.core.channel.v1.rs");
            }
        }
        pub mod commitment {
            pub mod v1 {
                include!("ibc.core.commitment.v1.rs");
            }
        }
        pub mod types {
            pub mod v1 {
                include!("ibc.core.types.v1.rs");
            }
        }
    }
}
