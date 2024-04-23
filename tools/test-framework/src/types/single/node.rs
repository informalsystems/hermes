/*!
   Type definition for a single running full node.
*/

use core::str::FromStr;
use core::time::Duration;
use eyre::eyre;
use eyre::Report as Error;
use ibc_relayer::chain::cosmos::config::CosmosSdkConfig;
use ibc_relayer::config;
use ibc_relayer::config::compat_mode::CompatMode;
use ibc_relayer::config::dynamic_gas::DynamicGasPrice;
use ibc_relayer::config::gas_multiplier::GasMultiplier;
use ibc_relayer::keyring::Store;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use std::sync::{Arc, RwLock};
use tendermint_rpc::Url;
use tendermint_rpc::WebSocketClientUrl;

use crate::chain::chain_type::ChainType as TestedChainType;
use crate::chain::driver::ChainDriver;
use crate::chain::exec::simple_exec;
use crate::ibc::denom::Denom;
use crate::prelude::TestConfig;
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
        test_config: &TestConfig,
        chain_number: usize,
    ) -> Result<config::ChainConfig, Error> {
        let native_token_number = chain_number % test_config.native_tokens.len();
        let hermes_keystore_dir = test_config
            .chain_store_dir
            .join("hermes_keyring")
            .as_path()
            .display()
            .to_string();

        let compat_mode = test_config.compat_modes.as_ref().map(|modes| {
            let mode = &modes[chain_number % modes.len()];
            CompatMode::from_str(mode).unwrap()
        });

        // Provenance requires a very high gas price
        let gas_price = match chain_type {
            TestedChainType::Provenance => config::GasPrice::new(
                5000.0,
                test_config.native_tokens[native_token_number].clone(),
            ),
            TestedChainType::Namada => {
                let denom = get_denom(&self.chain_driver.home_path)?;
                config::GasPrice::new(0.003, denom)
            }
            _ => config::GasPrice::new(
                0.003,
                test_config.native_tokens[native_token_number].clone(),
            ),
        };

        let chain_config = match chain_type {
            TestedChainType::Cosmos | TestedChainType::Provenance | TestedChainType::Evmos => {
                config::ChainConfig::CosmosSdk(CosmosSdkConfig {
                    id: self.chain_driver.chain_id.clone(),
                    rpc_addr: Url::from_str(&self.chain_driver.rpc_address())?,
                    grpc_addr: Url::from_str(&self.chain_driver.grpc_address())?,
                    event_source: config::EventSourceMode::Push {
                        url: WebSocketClientUrl::from_str(&self.chain_driver.websocket_address())?,
                        batch_delay: config::default::batch_delay(),
                    },
                    rpc_timeout: config::default::rpc_timeout(),
                    trusted_node: false,
                    genesis_restart: None,
                    account_prefix: self.chain_driver.account_prefix.clone(),
                    key_name: self.wallets.relayer.id.0.clone(),
                    key_store_type: Store::Test,
                    key_store_folder: Some(hermes_keystore_dir.into()),
                    store_prefix: "ibc".to_string(),
                    default_gas: None,
                    max_gas: Some(3000000),
                    gas_adjustment: None,
                    gas_multiplier: Some(GasMultiplier::unsafe_new(1.5)),
                    dynamic_gas_price: DynamicGasPrice::default(),
                    fee_granter: None,
                    max_msg_num: Default::default(),
                    max_tx_size: Default::default(),
                    max_grpc_decoding_size: config::default::max_grpc_decoding_size(),
                    query_packets_chunk_size: config::default::query_packets_chunk_size(),
                    max_block_time: Duration::from_secs(30),
                    clock_drift: Duration::from_secs(5),
                    trusting_period: Some(Duration::from_secs(14 * 24 * 3600)),
                    client_refresh_rate: config::default::client_refresh_rate(),
                    ccv_consumer_chain: false,
                    trust_threshold: Default::default(),
                    gas_price,
                    packet_filter: Default::default(),
                    address_type: chain_type.address_type(),
                    memo_prefix: Default::default(),
                    proof_specs: Default::default(),
                    extension_options: Default::default(),
                    sequential_batch_tx: false,
                    compat_mode,
                    clear_interval: None,
                })
            }
            TestedChainType::Namada => config::ChainConfig::Namada(CosmosSdkConfig {
                id: self.chain_driver.chain_id.clone(),
                rpc_addr: Url::from_str(&self.chain_driver.rpc_address())?,
                grpc_addr: Url::from_str(&self.chain_driver.grpc_address())?,
                event_source: config::EventSourceMode::Push {
                    url: WebSocketClientUrl::from_str(&self.chain_driver.websocket_address())?,
                    batch_delay: config::default::batch_delay(),
                },
                rpc_timeout: config::default::rpc_timeout(),
                trusted_node: false,
                genesis_restart: None,
                account_prefix: "".to_owned(),
                key_name: self.wallets.relayer.id.0.clone(),
                key_store_type: Store::Test,
                key_store_folder: Some(hermes_keystore_dir.into()),
                store_prefix: "ibc".to_string(),
                default_gas: None,
                max_gas: Some(3000000),
                gas_adjustment: None,
                gas_multiplier: Some(GasMultiplier::unsafe_new(1.2)),
                dynamic_gas_price: DynamicGasPrice::default(),
                fee_granter: None,
                max_msg_num: Default::default(),
                max_tx_size: Default::default(),
                max_grpc_decoding_size: config::default::max_grpc_decoding_size(),
                query_packets_chunk_size: config::default::query_packets_chunk_size(),
                max_block_time: Duration::from_secs(30),
                clock_drift: Duration::from_secs(5),
                trusting_period: Some(Duration::from_secs(1999)),
                client_refresh_rate: config::default::client_refresh_rate(),
                ccv_consumer_chain: false,
                trust_threshold: Default::default(),
                gas_price,
                packet_filter: Default::default(),
                address_type: chain_type.address_type(),
                memo_prefix: Default::default(),
                proof_specs: Default::default(),
                extension_options: Default::default(),
                sequential_batch_tx: false,
                compat_mode,
                clear_interval: None,
            }),
        };

        Ok(chain_config)
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

fn get_denom(home_path: &str) -> Result<String, Error> {
    let output = simple_exec(
        "namada",
        "namadaw",
        &["--base-dir", home_path, "find", "--alias", "nam"],
    )?
    .stdout;

    let words: Vec<&str> = output.split_whitespace().collect();

    if let Some(derived_index) = words.iter().position(|&w| w == "Established:") {
        if let Some(&denom) = words.get(derived_index + 1) {
            return Ok(denom.to_owned());
        }
        return Err(eyre!(
            "chain id is not 3 words after `Established:`: {output}"
        ));
    }
    Err(eyre!("could not find `Derived` in output: {output}"))
}

impl ExportEnv for FullNode {
    fn export_env(&self, writer: &mut impl EnvWriter) {
        self.chain_driver.export_env(writer);
        writer.write_env("DENOM", self.denom.as_str());
        self.wallets
            .export_env(&mut prefix_writer("WALLETS", writer));
    }
}
