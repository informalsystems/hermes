use ibc::core::ics24_host::identifier::ChainId;
use ibc_relayer::config::AddressType;

use crate::util::random::{random_u32, random_unused_tcp_port};

const COSMOS_HD_PATH: &str = "m/44'/118'/0'/0/0";
const EVMOS_HD_PATH: &str = "m/44'/60'/0'/0/0";

#[derive(Clone, Debug)]
pub enum ChainBinary {
    CosmosChain,
    EvmosChain,
}

impl ChainBinary {
    pub fn get_hd_path(&self) -> &str {
        match self {
            Self::CosmosChain => COSMOS_HD_PATH,
            Self::EvmosChain => EVMOS_HD_PATH,
        }
    }

    pub fn get_chain_id(&self, prefix: &str, use_random_id: bool) -> ChainId {
        match self {
            Self::CosmosChain => {
                if use_random_id {
                    ChainId::from_string(&format!("ibc-{}-{:x}", prefix, random_u32()))
                } else {
                    ChainId::from_string(&format!("ibc-{}", prefix))
                }
            }
            Self::EvmosChain => ChainId::from_string(&format!("evmos_9000-{}", prefix)),
        }
    }

    pub fn get_json_rpc_address(&self) -> (String, String) {
        let json_rpc_port = random_unused_tcp_port();
        match self {
            Self::CosmosChain => ("".to_owned(), "".to_owned()),
            Self::EvmosChain => (
                "--json-rpc.address".to_owned(),
                format!("localhost:{}", json_rpc_port),
            ),
        }
    }

    pub fn get_default_address_type(&self) -> AddressType {
        match self {
            Self::CosmosChain => AddressType::default(),
            Self::EvmosChain => AddressType::Ethermint {
                pk_type: "/ethermint.crypto.v1.ethsecp256k1.PubKey".to_string(),
            },
        }
    }
}

impl From<String> for ChainBinary {
    fn from(item: String) -> Self {
        match item {
            name if name.contains("gaiad") => ChainBinary::CosmosChain,
            name if name.contains("simd") => ChainBinary::CosmosChain,
            name if name.contains("wasmd") => ChainBinary::CosmosChain,
            name if name.contains("icad") => ChainBinary::CosmosChain,
            name if name.contains("evmosd") => ChainBinary::EvmosChain,
            _ => panic!("Unhandled chain binary `{}`", item),
        }
    }
}
