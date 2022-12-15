/*!
    Helper functions for bootstrapping two relayer chain handles
    with connected foreign clients.
*/

use eyre::Report as Error;
use ibc_relayer::chain::handle::{ChainHandle, CountingAndCachingChainHandle};
use ibc_relayer::config::Config;
use ibc_relayer::error::ErrorDetail as RelayerErrorDetail;
use ibc_relayer::foreign_client::{
    extract_client_id, CreateOptions as ClientOptions, ForeignClient,
};
use ibc_relayer::keyring::errors::ErrorDetail as KeyringErrorDetail;
use ibc_relayer::registry::SharedRegistry;
use ibc_relayer_types::core::ics24_host::identifier::ClientId;
use std::fs;
use std::path::Path;
use tracing::{debug, info};

use crate::relayer::driver::RelayerDriver;
use crate::types::binary::chains::ConnectedChains;
use crate::types::binary::foreign_client::ForeignClientPair;
use crate::types::config::TestConfig;
use crate::types::single::node::FullNode;
use crate::types::tagged::*;
use crate::types::wallet::{TestWallets, Wallet};
use crate::util::random::random_u64_range;

#[derive(Default)]
pub struct BootstrapClientOptions {
    pub client_options_a_to_b: ClientOptions,
    pub client_options_b_to_a: ClientOptions,
    pub pad_client_id_a_to_b: u64,
    pub pad_client_id_b_to_a: u64,
}

/// Bootstraps two relayer chain handles with connected foreign clients.
///
/// Returns a tuple consisting of the [`RelayerDriver`] and a
/// [`ConnectedChains`] object that contains the given
/// full nodes together with the corresponding two [`ChainHandle`]s and
/// [`ForeignClient`]s.
pub fn bootstrap_chains_with_full_nodes(
    test_config: &TestConfig,
    node_a: FullNode,
    node_b: FullNode,
    options: BootstrapClientOptions,
    config_modifier: impl FnOnce(&mut Config),
) -> Result<
    (
        RelayerDriver,
        ConnectedChains<impl ChainHandle, impl ChainHandle>,
    ),
    Error,
> {
    let mut config = Config::default();

    add_chain_config(&mut config, &node_a)?;
    add_chain_config(&mut config, &node_b)?;

    config_modifier(&mut config);

    let config_path = test_config.chain_store_dir.join("relayer-config.toml");

    save_relayer_config(&config, &config_path)?;

    let registry = new_registry(config.clone());

    // Pass in unique closure expressions `||{}` as the first argument so that
    // the returned chains are considered different types by Rust.
    // See [`spawn_chain_handle`] for more details.
    let handle_a = spawn_chain_handle(|| {}, &registry, &node_a)?;
    let handle_b = spawn_chain_handle(|| {}, &registry, &node_b)?;

    pad_client_ids(&handle_a, &handle_b, options.pad_client_id_a_to_b)?;
    pad_client_ids(&handle_b, &handle_a, options.pad_client_id_b_to_a)?;

    let foreign_clients = bootstrap_foreign_client_pair(&handle_a, &handle_b, options)?;

    let relayer = RelayerDriver {
        config_path,
        config,
        registry,
        hang_on_fail: test_config.hang_on_fail,
    };

    let chains = ConnectedChains::new(
        handle_a,
        handle_b,
        MonoTagged::new(node_a),
        MonoTagged::new(node_b),
        foreign_clients,
    );

    Ok((relayer, chains))
}

/// Bootstraps two relayer chain handles with connected foreign clients.
///
/// Returns a tuple consisting of the [`RelayerDriver`] and a
/// [`ConnectedChains`] object that contains the given
/// full nodes together with the corresponding two [`ChainHandle`]s and
/// [`ForeignClient`]s.
///
/// This method gives the caller a way to modify the relayer configuration
/// that is pre-generated from the configurations of the full nodes.
pub fn bootstrap_foreign_client_pair<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain_a: &ChainA,
    chain_b: &ChainB,
    options: BootstrapClientOptions,
) -> Result<ForeignClientPair<ChainA, ChainB>, Error> {
    let client_a_to_b = bootstrap_foreign_client(chain_a, chain_b, options.client_options_a_to_b)?;
    let client_b_to_a = bootstrap_foreign_client(chain_b, chain_a, options.client_options_b_to_a)?;
    Ok(ForeignClientPair::new(client_a_to_b, client_b_to_a))
}

pub fn bootstrap_foreign_client<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain_a: &ChainA,
    chain_b: &ChainB,
    client_options: ClientOptions,
) -> Result<ForeignClient<ChainB, ChainA>, Error> {
    let foreign_client =
        ForeignClient::restore(ClientId::default(), chain_b.clone(), chain_a.clone());

    let event = foreign_client.build_create_client_and_send(client_options)?;
    let client_id = extract_client_id(&event.event)?.clone();

    info!(
        "created foreign client from chain {} to chain {} with client id {} on chain {}",
        chain_a.id(),
        chain_b.id(),
        client_id,
        chain_b.id()
    );

    Ok(ForeignClient::restore(
        client_id,
        chain_b.clone(),
        chain_a.clone(),
    ))
}

pub fn pad_client_ids<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain_a: &ChainA,
    chain_b: &ChainB,
    pad_count: u64,
) -> Result<(), Error> {
    let foreign_client =
        ForeignClient::restore(ClientId::default(), chain_b.clone(), chain_a.clone());

    for i in 0..pad_count {
        debug!("creating new client id {} on chain {}", i + 1, chain_b.id());
        foreign_client.build_create_client_and_send(Default::default())?;
    }

    Ok(())
}

/**
   Spawn a new chain handle using the given [`SharedRegistry`] and
   [`FullNode`].

   The function accepts a proxy type `Seed` that should be unique
   accross multiple calls so that the returned [`ChainHandle`]
   have a unique type.

   For example, the following test should fail to compile:

   ```rust,compile_fail
   # use ibc_test_framework::bootstrap::binary::chain::spawn_chain_handle;
   fn same<T>(_: T, _: T) {}

   let chain_a = spawn_chain_handle(|| {}, todo!(), todo!()).unwrap();
   let chain_b = spawn_chain_handle(|| {}, todo!(), todo!()).unwrap();
   same(chain_a, chain_b); // error: chain_a and chain_b have different types
   ```

   The reason is that Rust would give each closure expression `||{}` a
   [unique anonymous type](https://doc.rust-lang.org/reference/types/closure.html).
   When we instantiate two chains with different closure types,
   the resulting values would be considered by Rust to have different types.

   With this we can treat `chain_a` and `chain_b` having different types
   so that we do not accidentally mix them up later in the code.
*/
pub fn spawn_chain_handle<Seed>(
    _: Seed,
    registry: &SharedRegistry<impl ChainHandle>,
    node: &FullNode,
) -> Result<impl ChainHandle, Error> {
    let chain_id = &node.chain_driver.chain_id;
    let handle = registry.get_or_spawn(chain_id)?;

    add_keys_to_chain_handle(&handle, &node.wallets)?;

    Ok(handle)
}

/**
   Add a wallet key to a [`ChainHandle`]'s key store.

   Note that if the [`ChainConfig`](ibc_relayer::config::ChainConfig) is
   configured to use in-memory store only, the added key would not be
   accessible through external CLI.
*/
pub fn add_key_to_chain_handle<Chain: ChainHandle>(
    chain: &Chain,
    wallet: &Wallet,
) -> Result<(), Error> {
    let res = chain.add_key(wallet.id.0.clone(), wallet.key.clone().into());

    // Ignore error if chain handle already have the given key
    match res {
        Err(e) => match e.detail() {
            RelayerErrorDetail::KeyBase(e2) => match e2.source {
                KeyringErrorDetail::KeyAlreadyExist(_) => Ok(()),
                _ => Err(e.into()),
            },
            _ => Err(e.into()),
        },
        Ok(()) => Ok(()),
    }
}

/**
   Add multiple wallets provided in [`TestWallets`] into the
   [`ChainHandle`]'s key store.
*/
pub fn add_keys_to_chain_handle<Chain: ChainHandle>(
    chain: &Chain,
    wallets: &TestWallets,
) -> Result<(), Error> {
    add_key_to_chain_handle(chain, &wallets.relayer)?;
    add_key_to_chain_handle(chain, &wallets.user1)?;
    add_key_to_chain_handle(chain, &wallets.user2)?;

    Ok(())
}

/**
   Create a new [`SharedRegistry`] that uses [`CountingAndCachingChainHandle`]
   as the [`ChainHandle`] implementation.
*/
pub fn new_registry(config: Config) -> SharedRegistry<CountingAndCachingChainHandle> {
    <SharedRegistry<CountingAndCachingChainHandle>>::new(config)
}

/**
   Generate [`ChainConfig`](ibc_relayer::config::ChainConfig) from a running
   [`FullNode`] and add it to the relayer's [`Config`].
*/
pub fn add_chain_config(config: &mut Config, running_node: &FullNode) -> Result<(), Error> {
    let chain_config = running_node.generate_chain_config(&running_node.chain_driver.chain_type)?;

    config.chains.push(chain_config);
    Ok(())
}

/**
   Save a relayer's [`Config`] to the filesystem to make it accessible
   through external CLI.
*/
pub fn save_relayer_config(config: &Config, config_path: &Path) -> Result<(), Error> {
    let config_str = toml::to_string_pretty(&config)?;

    fs::write(config_path, &config_str)?;

    info!(
        "written hermes config.toml to {}:\n{}",
        config_path.display(),
        config_str
    );

    Ok(())
}

impl BootstrapClientOptions {
    /// Overrides options for the foreign client connecting chain A to chain B.
    pub fn client_options_a_to_b(mut self, options: ClientOptions) -> Self {
        self.client_options_a_to_b = options;
        self
    }

    /// Overrides options for the foreign client connecting chain B to chain A.
    pub fn client_options_b_to_a(mut self, options: ClientOptions) -> Self {
        self.client_options_b_to_a = options;
        self
    }

    pub fn bootstrap_with_random_ids(mut self, bootstrap_with_random_ids: bool) -> Self {
        if bootstrap_with_random_ids {
            self.pad_client_id_b_to_a = random_u64_range(1, 6);
            self.pad_client_id_a_to_b = random_u64_range(1, 6);
        } else {
            self.pad_client_id_b_to_a = 0;
            self.pad_client_id_a_to_b = 1;
        }

        self
    }
}
