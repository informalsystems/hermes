pub mod cosmos {
    pub mod base {
        pub mod tendermint {
            pub mod v1beta1 {
                include!("prost/cosmos.base.tendermint.v1beta1.rs");
            }
        }
        pub mod reflection {
            pub mod v1beta1 {
                include!("prost/cosmos.base.reflection.v1beta1.rs");
            }
        }
    }
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

    pub mod tx {
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
        pub mod client {
            pub mod v1 {
                include!("prost/ibc.core.client.v1.rs");
            }
        }

        pub mod channel {
            pub mod v1 {
                include!("prost/ibc.core.channel.v1.rs");
            }
        }

        pub mod connection {
            pub mod v1 {
                include!("prost/ibc.core.connection.v1.rs");
            }
        }
    }
}
