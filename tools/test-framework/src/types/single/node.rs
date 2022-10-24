/*!
   Type definition for a single running full node.
*/

use core::str::FromStr;
use core::time::Duration;
use eyre::eyre;
use eyre::Report as Error;
use ibc_relayer::chain::ChainType;
use ibc_relayer::config;
use ibc_relayer::keyring::Store;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use std::sync::{Arc, RwLock};
use tendermint_rpc::Url;

use crate::chain::chain_type::ChainType as TestedChainType;
use crate::chain::driver::ChainDriver;
use crate::ibc::denom::Denom;
use crate::types::env::{prefix_writer, EnvWriter, ExportEnv};
use crate::types::process::ChildProcess;
use crate::types::tagged::*;
use crate::types::wallet::TestWallets;

pub type TaggedFullNode<Chain> = MonoTagged<Chain, FullNode>;

pub type TaggedFullNodeRef<'a, Chain> = MonoTagged<Chain, &'a FullNode>;

/**
   Represents a full node running as a child process managed by the test.
*/
#[derive(Clone)]
pub struct FullNode {
    /**
       The [`ChainDriver`] used to communicate with the full node.
    */
    pub chain_driver: ChainDriver,

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

    /**
       The child process that is running the full node.

       The full node is killed when the `Arc` shared pointer is dropped.

       Test authors can acquire the child process and kill the full node
       in the middle of tests using [`kill`](FullNode::kill).
    */
    pub process: Arc<RwLock<ChildProcess>>,
}

/**
   Extra methods for [`FullNode`] that is [tagged](crate::types::tagged).

   This trait is auto implemented for `MonoTagged<Chain, FullNode>` so
   that we can call methods on it directly.
*/
pub trait TaggedFullNodeExt<Chain> {
    /// Get the [`ChainId`] tagged with the given `Chain`.
    fn chain_id(&self) -> MonoTagged<Chain, &ChainId>;

    /// Get the [`ChainDriver`] tagged with the given `Chain`.
    fn chain_driver(&self) -> MonoTagged<Chain, &ChainDriver>;

    /// Get the [`TestWallets`] tagged with the given `Chain`.
    fn wallets(&self) -> MonoTagged<Chain, &TestWallets>;

    /// Get the [`Denom`] tagged with the given `Chain`.
    fn denom(&self) -> MonoTagged<Chain, &Denom>;
}

impl<Chain> TaggedFullNodeExt<Chain> for MonoTagged<Chain, FullNode> {
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

impl<'a, Chain> TaggedFullNodeExt<Chain> for MonoTagged<Chain, &'a FullNode> {
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
    /**
       Generate the relayer's chain config based on the configuration of
       the full node.
    */
    pub fn generate_chain_config(
        &self,
        chain_type: &TestedChainType,
    ) -> Result<config::ChainConfig, Error> {
        Ok(config::ChainConfig {
            id: self.chain_driver.chain_id.clone(),
            r#type: ChainType::CosmosSdk,
            rpc_addr: Url::from_str(&self.chain_driver.rpc_address())?,
            websocket_addr: Url::from_str(&self.chain_driver.websocket_address())?,
            grpc_addr: Url::from_str(&self.chain_driver.grpc_address())?,
            rpc_timeout: Duration::from_secs(10),
            account_prefix: self.chain_driver.account_prefix.clone(),
            key_name: self.wallets.relayer.id.0.clone(),

            // By default we use in-memory key store to avoid polluting
            // ~/.hermes/keys. See
            // https://github.com/informalsystems/hermes/issues/1541
            key_store_type: Store::Memory,

            store_prefix: "ibc".to_string(),
            default_gas: None,
            max_gas: Some(3000000),
            gas_adjustment: None,
            gas_multiplier: Default::default(),
            fee_granter: None,
            max_msg_num: Default::default(),
            max_tx_size: Default::default(),
            max_block_time: Duration::from_secs(30),
            clock_drift: Duration::from_secs(5),
            trusting_period: Some(Duration::from_secs(14 * 24 * 3600)),
            trust_threshold: Default::default(),
            gas_price: config::GasPrice::new(0.001, "stake".to_string()),
            packet_filter: Default::default(),
            address_type: chain_type.address_type(),
            memo_prefix: Default::default(),
            proof_specs: Default::default(),
            extension_options: Default::default(),
            sequential_batch_tx: false,
        })
    }

    /**
       Kill the underlying child process of the full node, thereby terminating it.

       Test writers can use this to kill the full node in the middle of tests, and
       then restart it using
       [`ChainDriver::start`](crate::chain::ext::bootstrap::ChainBootstrapMethodsExt::start).
    */
    pub fn kill(&self) -> Result<(), Error> {
        self.process
            .write()
            .map_err(|_| eyre!("poisoned mutex"))?
            .kill()
    }
}

impl ExportEnv for FullNode {
    fn export_env(&self, writer: &mut impl EnvWriter) {
        self.chain_driver.export_env(writer);
        writer.write_env("DENOM", self.denom.as_str());
        self.wallets
            .export_env(&mut prefix_writer("WALLETS", writer));
    }
}
