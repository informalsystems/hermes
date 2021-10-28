use ibc::core::ics24_host::identifier::ChainId;

use super::driver::ChainDriver;
use crate::config::TestConfig;
use crate::util::random::{random_u32, random_unused_tcp_port};

#[derive(Debug)]
pub struct ChainBuilder {
    pub command_path: String,

    pub base_store_dir: String,
}

impl ChainBuilder {
    pub fn new(command_path: &str, base_store_dir: &str) -> Self {
        Self {
            command_path: command_path.to_string(),
            base_store_dir: base_store_dir.to_string(),
        }
    }

    pub fn new_with_config(config: &TestConfig) -> Self {
        Self::new(&config.chain_command_path, &config.chain_store_dir)
    }

    pub fn new_chain(&self) -> ChainDriver {
        let chain_num = random_u32();
        let chain_id = ChainId::from_string(&format!("ibc-{:x}", chain_num));

        let rpc_port = random_unused_tcp_port();
        let grpc_port = random_unused_tcp_port();
        let p2p_port = random_unused_tcp_port();

        let home_path = format!("{}/{}", self.base_store_dir, chain_id);

        ChainDriver::new(
            self.command_path.clone(),
            chain_id,
            home_path,
            rpc_port,
            grpc_port,
            p2p_port,
        )
    }
}
