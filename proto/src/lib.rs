//! ibc-proto library gives the developer access to the Cosmos SDK IBC proto-defined structs.

// Todo: automate the creation of this module setup based on the dots in the filenames.
//  This module setup is necessary because the generated code contains "super::" calls for dependencies.

#![deny(warnings, trivial_casts, trivial_numeric_casts, unused_import_braces)]
#![allow(clippy::large_enum_variant)]
#![forbid(unsafe_code)]
#![doc(html_root_url = "https://docs.rs/ibc-proto/0.1.0")]

pub mod cosmos {
    pub mod base {
        pub mod v1beta1 {
            include!("prost/cosmos.base.v1beta1.rs");
        }
        pub mod abci {
            pub mod v1beta1 {
                include!("prost/cosmos.base.abci.v1beta1.rs");
            }
        }
        pub mod crypto {
            pub mod v1beta1 {
                include!("prost/cosmos.base.crypto.v1beta1.rs");
            }
        }
        pub mod kv {
            pub mod v1beta1 {
                include!("prost/cosmos.base.kv.v1beta1.rs");
            }
        }
        pub mod query {
            pub mod v1beta1 {
                include!("prost/cosmos.base.query.v1beta1.rs");
            }
        }
        pub mod reflection {
            pub mod v1beta1 {
                include!("prost/cosmos.base.reflection.v1beta1.rs");
            }
        }
        pub mod simulate {
            pub mod v1beta1 {
                include!("prost/cosmos.base.simulate.v1beta1.rs");
            }
        }
        pub mod store {
            pub mod v1beta1 {
                include!("prost/cosmos.base.store.v1beta1.rs");
            }
        }
    }
    pub mod tx {
        pub mod v1beta1 {
            include!("prost/cosmos.tx.v1beta1.rs");
        }
        pub mod signing {
            pub mod v1beta1 {
                include!("prost/cosmos.tx.signing.v1beta1.rs");
            }
        }
    }
}

pub mod ibc {
    pub mod client {
        include!("prost/ibc.client.rs");
    }
    pub mod channel {
        include!("prost/ibc.channel.rs");
    }
    pub mod commitment {
        include!("prost/ibc.commitment.rs");
    }
    pub mod connection {
        include!("prost/ibc.connection.rs");
    }
    pub mod localhost {
        include!("prost/ibc.localhost.rs");
    }
    pub mod tendermint {
        include!("prost/ibc.tendermint.rs");
    }
    pub mod transfer {
        include!("prost/ibc.transfer.rs");
    }
    pub mod types {
        include!("prost/ibc.types.rs");
    }
    pub mod mock {
        include!("prost/ibc.mock.rs");
    }
}

pub mod ics23 {
    include!("prost/ics23.rs");
}

pub mod tendermint {
    pub mod abci {
        include!("prost/tendermint.abci.rs");
    }
    pub mod crypto {
        include!("prost/tendermint.crypto.rs");
    }
    pub mod libs {
        pub mod bits {
            include!("prost/tendermint.libs.bits.rs");
        }
    }
    pub mod types {
        include!("prost/tendermint.types.rs");
    }
    pub mod version {
        include!("prost/tendermint.version.rs");
    }
}

mod domaintype;
pub use domaintype::DomainType;

mod error;
pub use error::{Error, Kind};

// Re-export the DomainType derive macro #[derive(DomainType)]
#[cfg(feature = "ibc-proto-derive")]
#[doc(hidden)]
pub use ibc_proto_derive::DomainType;
