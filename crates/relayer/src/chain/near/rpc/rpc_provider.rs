pub const NEAR_OFFICIAL_MAINNET_RPC_URL: &str = "https://rpc.mainnet.near.org";
pub const NEAR_OFFICIAL_TESTNET_RPC_URL: &str = "https://rpc.testnet.near.org";

pub const INFURA_MAINNET_RPC_URL: &str = "https://public-rpc.blockpi.io/http/near";
pub const INFURA_TESTNET_RPC_URL: &str =
    "https://near-testnet.infura.io/v3/4f80a04e6eb2437a9ed20cb874e10d55";

#[derive(Debug, Clone)]
pub enum NearEnv {
    Testnet,
    Mainnet,
}

pub enum RpcProvider {
    NearOfficial,
    Infura,
}

impl RpcProvider {
    pub fn get_rpc_by_env(&self, env: &NearEnv) -> &str {
        match self {
            RpcProvider::NearOfficial => match env {
                NearEnv::Testnet => NEAR_OFFICIAL_TESTNET_RPC_URL,
                NearEnv::Mainnet => NEAR_OFFICIAL_MAINNET_RPC_URL,
            },
            RpcProvider::Infura => match env {
                NearEnv::Testnet => INFURA_TESTNET_RPC_URL,
                NearEnv::Mainnet => INFURA_MAINNET_RPC_URL,
            },
        }
    }
}
