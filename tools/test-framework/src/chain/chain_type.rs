use core::str::FromStr;
use ibc_relayer::config::AddressType;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;

use crate::error::Error;
use crate::util::random::{random_u32, random_unused_tcp_port};

const COSMOS_HD_PATH: &str = "m/44'/118'/0'/0/0";
const EVMOS_HD_PATH: &str = "m/44'/60'/0'/0/0";
const NAMADA_HD_PATH: &str = "m/44'/877'/0'/0'/0'";

#[derive(Clone, Debug)]
pub enum ChainType {
    Cosmos,
    Evmos,
    Namada,
}

impl ChainType {
    pub fn hd_path(&self) -> &str {
        match self {
            Self::Cosmos => COSMOS_HD_PATH,
            Self::Evmos => EVMOS_HD_PATH,
            Self::Namada => NAMADA_HD_PATH,
        }
    }

    pub fn chain_id(&self, prefix: &str, use_random_id: bool) -> ChainId {
        match self {
            Self::Cosmos => {
                if use_random_id {
                    ChainId::from_string(&format!("ibc-{}-{:x}", prefix, random_u32()))
                } else {
                    //ChainId::from_string(&format!("ibc{prefix}"))
                    ChainId::from_string(&format!("gaia-0"))
                }
            }
            Self::Evmos => ChainId::from_string(&format!("evmos_9000-{prefix}")),
            Self::Namada => ChainId::from_string(&format!("namada-{prefix}")),
        }
    }

    // Extra arguments required to run `<chain binary> start`
    pub fn extra_start_args(&self) -> Vec<String> {
        let mut res = vec![];
        let json_rpc_port = random_unused_tcp_port();
        match self {
            Self::Cosmos | Self::Namada => {}
            Self::Evmos => {
                res.push("--json-rpc.address".to_owned());
                res.push(format!("localhost:{json_rpc_port}"));
            }
        }
        res
    }

    pub fn address_type(&self) -> AddressType {
        match self {
            Self::Cosmos => AddressType::default(),
            Self::Evmos => AddressType::Ethermint {
                pk_type: "/ethermint.crypto.v1.ethsecp256k1.PubKey".to_string(),
            },
            Self::Namada => AddressType::default(),
        }
    }
}

impl FromStr for ChainType {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            name if name.contains("gaiad") => Ok(ChainType::Cosmos),
            name if name.contains("simd") => Ok(ChainType::Cosmos),
            name if name.contains("wasmd") => Ok(ChainType::Cosmos),
            name if name.contains("icad") => Ok(ChainType::Cosmos),
            name if name.contains("evmosd") => Ok(ChainType::Evmos),
            name if name.contains("namada") => Ok(ChainType::Namada),
            _ => Ok(ChainType::Cosmos),
        }
    }
}
