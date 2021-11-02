use core::str::FromStr;
use core::time::Duration;
use eyre::Report as Error;
use ibc::core::ics24_host::identifier::ChainId;
use ibc_relayer::config;
use ibc_relayer::keyring::Store;
use tendermint_rpc::Url;

use crate::chain::driver::ChainDriver;
use crate::ibc::denom::Denom;
use crate::tagged::*;
use crate::types::process::ChildProcess;
use crate::types::wallets::ChainWallets;

pub struct RunningNode {
    pub chain_driver: ChainDriver,
    pub chain_process: ChildProcess,
    pub denom: Denom,
    pub wallets: ChainWallets,
}

impl<Chain> MonoTagged<Chain, RunningNode> {
    pub fn chain_id<'a>(&'a self) -> MonoTagged<Chain, &'a ChainId> {
        self.map_ref(|c| &c.chain_driver.chain_id)
    }

    pub fn chain_driver<'a>(&'a self) -> MonoTagged<Chain, &'a ChainDriver> {
        self.map_ref(|c| &c.chain_driver)
    }

    pub fn wallets<'a>(&'a self) -> MonoTagged<Chain, &'a ChainWallets> {
        self.map_ref(|c| &c.wallets)
    }

    pub fn denom<'a>(&'a self) -> MonoTagged<Chain, &'a Denom> {
        self.map_ref(|c| &c.denom)
    }
}

impl RunningNode {
    pub fn generate_chain_config(&self) -> Result<config::ChainConfig, Error> {
        Ok(config::ChainConfig {
            id: self.chain_driver.chain_id.clone(),
            rpc_addr: Url::from_str(&self.chain_driver.rpc_address())?,
            websocket_addr: Url::from_str(&self.chain_driver.websocket_address())?,
            grpc_addr: Url::from_str(&self.chain_driver.grpc_address())?,
            rpc_timeout: Duration::from_secs(10),
            account_prefix: "cosmos".to_string(),
            key_name: self.wallets.relayer.id.0.clone(),
            key_store_type: Store::Memory,
            store_prefix: "ibc".to_string(),
            default_gas: None,
            max_gas: Some(3000000),
            gas_adjustment: Some(0.1),
            max_msg_num: Default::default(),
            max_tx_size: Default::default(),
            max_block_time: Default::default(),
            clock_drift: Duration::from_secs(5),
            trusting_period: Some(Duration::from_secs(14 * 24 * 3600)),
            trust_threshold: Default::default(),
            gas_price: config::GasPrice::new(0.001, "stake".to_string()),
            packet_filter: Default::default(),
            address_type: Default::default(),
            memo_prefix: Default::default(),
        })
    }
}
