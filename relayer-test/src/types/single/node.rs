/*!
   Type definition for a single running full node.
*/

use core::str::FromStr;
use core::time::Duration;
use eyre::Report as Error;
use ibc::core::ics24_host::identifier::ChainId;
use ibc_relayer::config;
use ibc_relayer::keyring::Store;
use tendermint_rpc::Url;

use crate::chain::driver::ChainDriver;
use crate::ibc::denom::Denom;
use crate::types::process::ChildProcess;
use crate::types::tagged::*;
use crate::types::wallet::TestWallets;

/**
   Represents a full node running as a child process managed by the test.
*/
pub struct FullNode {
    /**
       The [`ChainDriver`] used to communicate with the full node.
    */
    pub chain_driver: ChainDriver,

    /**
       The type holding the underlying child process, which will kill the
       full node when [`FullNode`] is dropped.
    */
    pub chain_process: Option<ChildProcess>,

    /**
       The currency denomination which the wallets have been loaded
       with initial balance during the chain setup.
    */
    pub denom: Denom,

    /**
       The test wallets with more than sufficient account balance that
       can be used for testing.
    */
    pub wallets: TestWallets,
}

/**
   Extra methods for [`FullNode`] that is [tagged](crate::types::tagged).

   This trait is auto implemented for `MonoTagged<Chain, FullNode>` so
   that we can call methods on it directly.
*/
pub trait TaggedFullNode<Chain> {
    /// Get the [`ChainId`] tagged with the given `Chain`.
    fn chain_id(&self) -> MonoTagged<Chain, &ChainId>;

    /// Get the [`ChainDriver`] tagged with the given `Chain`.
    fn chain_driver(&self) -> MonoTagged<Chain, &ChainDriver>;

    /// Get the [`TestWallets`] tagged with the given `Chain`.
    fn wallets(&self) -> MonoTagged<Chain, &TestWallets>;

    /// Get the [`Denom`] tagged with the given `Chain`.
    fn denom(&self) -> MonoTagged<Chain, &Denom>;
}

impl<Chain> TaggedFullNode<Chain> for MonoTagged<Chain, FullNode> {
    fn chain_id(&self) -> MonoTagged<Chain, &ChainId> {
        self.map_ref(|c| &c.chain_driver.chain_id)
    }

    fn chain_driver(&self) -> MonoTagged<Chain, &ChainDriver> {
        self.map_ref(|c| &c.chain_driver)
    }

    fn wallets(&self) -> MonoTagged<Chain, &TestWallets> {
        self.map_ref(|c| &c.wallets)
    }

    fn denom(&self) -> MonoTagged<Chain, &Denom> {
        self.map_ref(|c| &c.denom)
    }
}

impl<'a, Chain> TaggedFullNode<Chain> for MonoTagged<Chain, &'a FullNode> {
    fn chain_id(&self) -> MonoTagged<Chain, &ChainId> {
        self.map_ref(|c| &c.chain_driver.chain_id)
    }

    fn chain_driver(&self) -> MonoTagged<Chain, &ChainDriver> {
        self.map_ref(|c| &c.chain_driver)
    }

    fn wallets(&self) -> MonoTagged<Chain, &TestWallets> {
        self.map_ref(|c| &c.wallets)
    }

    fn denom(&self) -> MonoTagged<Chain, &Denom> {
        self.map_ref(|c| &c.denom)
    }
}

impl FullNode {
    pub fn replicate(&self) -> Self {
        Self {
            chain_driver: self.chain_driver.clone(),
            chain_process: None,
            denom: self.denom.clone(),
            wallets: self.wallets.clone(),
        }
    }

    /**
       Generate the relayer's chain config based on the configuration of
       the full node.
    */
    pub fn generate_chain_config(&self) -> Result<config::ChainConfig, Error> {
        Ok(config::ChainConfig {
            id: self.chain_driver.chain_id.clone(),
            rpc_addr: Url::from_str(&self.chain_driver.rpc_address())?,
            websocket_addr: Url::from_str(&self.chain_driver.websocket_address())?,
            grpc_addr: Url::from_str(&self.chain_driver.grpc_address())?,
            rpc_timeout: Duration::from_secs(10),
            account_prefix: "cosmos".to_string(),
            key_name: self.wallets.relayer.id.0.clone(),

            // By default we use in-memory key store to avoid polluting
            // ~/.hermes/keys. See
            // https://github.com/informalsystems/ibc-rs/issues/1541
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
