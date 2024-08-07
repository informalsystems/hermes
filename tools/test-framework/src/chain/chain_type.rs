use core::str::FromStr;
use ibc_relayer::config::AddressType;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;

use crate::error::Error;
use crate::util::random::{random_u32, random_unused_tcp_port};

const COSMOS_HD_PATH: &str = "m/44'/118'/0'/0/0";
const EVMOS_HD_PATH: &str = "m/44'/60'/0'/0/0";
const PROVENANCE_HD_PATH: &str = "m/44'/505'/0'/0/0";

#[derive(Clone, Debug)]
pub enum ChainType {
    Cosmos { dynamic_fee: bool },
    Osmosis,
    Evmos,
    Provenance,
    Injective,
}

impl ChainType {
    pub fn hd_path(&self) -> &str {
        match self {
            Self::Cosmos { dynamic_fee: _ } | Self::Osmosis => COSMOS_HD_PATH,
            Self::Evmos | Self::Injective => EVMOS_HD_PATH,
            Self::Provenance => PROVENANCE_HD_PATH,
        }
    }

    pub fn chain_id(&self, prefix: &str, use_random_id: bool) -> ChainId {
        match self {
            Self::Cosmos { dynamic_fee: _ } => {
                if use_random_id {
                    ChainId::from_string(&format!("ibc-{}-{:x}", prefix, random_u32()))
                } else {
                    ChainId::from_string(&format!("ibc{prefix}"))
                }
            }
            Self::Osmosis => {
                if use_random_id {
                    ChainId::from_string(&format!("osmosis-{}-{:x}", prefix, random_u32()))
                } else {
                    ChainId::from_string(&format!("osmosis{prefix}"))
                }
            }
            Self::Injective => ChainId::from_string(&format!("injective-{prefix}")),
            Self::Evmos => ChainId::from_string(&format!("evmos_9000-{prefix}")),
            Self::Provenance => ChainId::from_string(&format!("pio-mainnet-{prefix}")),
        }
    }

    // Extra arguments required to run `<chain binary> start`
    pub fn extra_start_args(&self) -> Vec<String> {
        let mut res = vec![];
        let json_rpc_port = random_unused_tcp_port();
        match self {
            Self::Cosmos { dynamic_fee: _ } | Self::Injective | Self::Provenance => {}
            Self::Osmosis => {
                res.push("--reject-config-defaults".to_owned());
            }
            Self::Evmos => {
                res.push("--json-rpc.address".to_owned());
                res.push(format!("localhost:{json_rpc_port}"));
            }
        }
        res
    }

    // Extra arguments required to run `<chain binary> add-genesis-account`
    pub fn extra_add_genesis_account_args(&self, chain_id: &ChainId) -> Vec<String> {
        let mut res = vec![];
        match self {
            Self::Cosmos { dynamic_fee: _ } | Self::Osmosis | Self::Evmos | Self::Provenance => {}
            Self::Injective => {
                res.push("--chain-id".to_owned());
                res.push(format!("{chain_id}"));
            }
        }
        res
    }

    pub fn address_type(&self) -> AddressType {
        match self {
            Self::Cosmos { dynamic_fee: _ } | Self::Osmosis | Self::Provenance => {
                AddressType::default()
            }
            Self::Evmos => AddressType::Ethermint {
                pk_type: "/ethermint.crypto.v1.ethsecp256k1.PubKey".to_string(),
            },
            Self::Injective => AddressType::Ethermint {
                pk_type: "/injective.crypto.v1beta1.ethsecp256k1.PubKey".to_string(),
            },
        }
    }

    pub fn enable_dynamic_fee(&self) -> bool {
        matches!(self, Self::Cosmos { dynamic_fee } if *dynamic_fee)
    }
}

impl FromStr for ChainType {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            name if name.contains("gaiad") || name.contains("neutrond") => {
                Ok(ChainType::Cosmos { dynamic_fee: true })
            }
            name if name.contains("evmosd") => Ok(ChainType::Evmos),
            name if name.contains("injectived") => Ok(ChainType::Injective),
            name if name.contains("provenanced") => Ok(ChainType::Provenance),
            name if name.contains("osmosisd") => Ok(ChainType::Osmosis),
            _ => Ok(ChainType::Cosmos { dynamic_fee: false }),
        }
    }
}
