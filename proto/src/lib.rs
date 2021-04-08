//! ibc-proto library gives the developer access to the Cosmos SDK IBC proto-defined structs.

// Todo: automate the creation of this module setup based on the dots in the filenames.
//  This module setup is necessary because the generated code contains "super::" calls for dependencies.

#![deny(warnings, trivial_casts, trivial_numeric_casts, unused_import_braces)]
#![allow(clippy::large_enum_variant)]
#![forbid(unsafe_code)]
#![doc(html_root_url = "https://docs.rs/ibc-proto/0.7.0")]

/// The version (commit hash) of the Cosmos SDK used when generating this library.
pub const COSMOS_SDK_VERSION: &str = include_str!("prost/COSMOS_SDK_COMMIT");
pub const COSMOS_IBC_VERSION: &str = include_str!("prost/COSMOS_IBC_COMMIT");

pub mod cosmos {
    pub mod auth {
        pub mod v1beta1 {
            include!("prost/cosmos.auth.v1beta1.rs");
        }
    }
    pub mod staking {
        pub mod v1beta1 {
            include!("prost/cosmos.staking.v1beta1.rs");
        }
    }
    pub mod base {
        pub mod abci {
            pub mod v1beta1 {
                include!("prost/cosmos.base.abci.v1beta1.rs");
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
        pub mod store {
            pub mod v1beta1 {
                include!("prost/cosmos.base.store.v1beta1.rs");
            }
        }
        pub mod v1beta1 {
            include!("prost/cosmos.base.v1beta1.rs");
        }
    }
    pub mod crypto {
        pub mod multisig {
            pub mod v1beta1 {
                include!("prost/cosmos.crypto.multisig.v1beta1.rs");
            }
        }
    }
    pub mod tx {
        pub mod signing {
            pub mod v1beta1 {
                include!("prost/cosmos.tx.signing.v1beta1.rs");
            }
        }
        pub mod v1beta1 {
            include!("prost/cosmos.tx.v1beta1.rs");
        }
    }
    pub mod upgrade {
        pub mod v1beta1 {
            include!("prost/cosmos.upgrade.v1beta1.rs");
        }
    }
    pub mod gov {
        pub mod v1beta1 {
            include!("prost/cosmos.gov.v1beta1.rs");
        }
    }
}

pub mod ibc {
    pub mod apps {
        pub mod transfer {
            pub mod v1 {
                include!("prost/ibc.applications.transfer.v1.rs");
            }
        }
    }
    pub mod core {
        pub mod channel {
            pub mod v1 {
                include!("prost/ibc.core.channel.v1.rs");
            }
        }
        pub mod client {
            pub mod v1 {
                include!("prost/ibc.core.client.v1.rs");
            }
        }
        pub mod commitment {
            pub mod v1 {
                include!("prost/ibc.core.commitment.v1.rs");
            }
        }
        pub mod connection {
            pub mod v1 {
                include!("prost/ibc.core.connection.v1.rs");
            }
        }
        pub mod types {
            pub mod v1 {
                include!("prost/ibc.core.types.v1.rs");
            }
        }
    }
    pub mod lightclients {
        pub mod localhost {
            pub mod v1 {
                include!("prost/ibc.lightclients.localhost.v1.rs");
            }
        }
        pub mod solomachine {
            pub mod v1 {
                include!("prost/ibc.lightclients.solomachine.v1.rs");
            }
        }
        pub mod tendermint {
            pub mod v1 {
                include!("prost/ibc.lightclients.tendermint.v1.rs");
            }
        }
    }
    pub mod mock {
        include!("prost/ibc.mock.rs");
    }
}

pub mod ics23 {
    include!("prost/ics23.rs");
}
