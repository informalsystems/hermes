/*!
    Helper functions for bootstrapping two relayer chain handles
    with connected foreign clients.
*/
use eyre::Report as Error;
use ibc::core::ics24_host::identifier::ClientId;
use ibc_relayer::chain::handle::{ChainHandle, ProdChainHandle};
use ibc_relayer::config::{Config, SharedConfig};
use ibc_relayer::foreign_client::{extract_client_id, ForeignClient};
use ibc_relayer::registry::SharedRegistry;
use std::fs;
use std::path::Path;
use std::sync::Arc;
use std::sync::RwLock;
use tracing::{debug, info};

use crate::types::binary::chains::ConnectedChains;
use crate::types::config::TestConfig;
use crate::types::single::node::FullNode;
use crate::types::tagged::*;
use crate::types::wallet::{TestWallets, Wallet};
use crate::util::random::random_u64_range;

/**
   Bootstraps two relayer chain handles with connected foreign clients.

   Takes two [`FullNode`] values representing two different running
   full nodes, and return a [`ConnectedChains`] that contain the given
   full nodes together with the corresponding two [`ChainHandle`]s and
   [`ForeignClient`]s. Also accepts an [`FnOnce`] closure that modifies
   the relayer's [`Config`] before the chain handles are initialized.
*/
pub fn boostrap_chain_pair_with_nodes(
    test_config: &TestConfig,
    node_a: FullNode,
    node_b: FullNode,
    config_modifier: impl FnOnce(&mut Config),
) -> Result<ConnectedChains<impl ChainHandle, impl ChainHandle>, Error> {
    let mut config = Config::default();

    add_chain_config(&mut config, &node_a)?;
    add_chain_config(&mut config, &node_b)?;

    config_modifier(&mut config);

    let config_path = test_config.chain_store_dir.join("relayer-config.toml");

    save_relayer_config(&config, &config_path)?;

    let config = Arc::new(RwLock::new(config));

    let registry = new_registry(config.clone());

    // Pass in unique closure expressions `||{}` as the first argument so that
    // the returned chains are considered different types by Rust.
    // See [`spawn_chain_handle`] for more details.
    let handle_a = spawn_chain_handle(|| {}, &registry, &node_a)?;
    let handle_b = spawn_chain_handle(|| {}, &registry, &node_b)?;

    if test_config.bootstrap_with_random_ids {
        pad_client_ids(&handle_a, &handle_b)?;
        pad_client_ids(&handle_b, &handle_a)?;
    }

    let client_a_to_b = bootstrap_foreign_client(&handle_a, &handle_b)?;
    let client_b_to_a = bootstrap_foreign_client(&handle_b, &handle_a)?;

    let chains = ConnectedChains::new(
        config_path,
        config,
        registry,
        handle_a,
        handle_b,
        MonoTagged::new(node_a),
        MonoTagged::new(node_b),
        client_a_to_b,
        client_b_to_a,
    );

    Ok(chains)
}

/**
   Work similary to [`boostrap_chain_pair_with_nodes`], but bootstraps a
   single chain to be connected with itself.

   Self-connected chains are in fact allowed in IBC. Although we do not
   have a clear use case for it yet, it is important to verify that
   tests that pass with two connected chains should also pass with
   self-connected chains.

   Returns a [`ConnectedChains`] with the two underlying chains
   being the same chain.
*/
pub fn boostrap_self_connected_chain(
    test_config: &TestConfig,
    node: FullNode,
    config_modifier: impl FnOnce(&mut Config),
) -> Result<ConnectedChains<impl ChainHandle, impl ChainHandle>, Error> {
    let mut config = Config::default();

    add_chain_config(&mut config, &node)?;

    config_modifier(&mut config);

    let config_path = test_config.chain_store_dir.join("relayer-config.toml");

    save_relayer_config(&config, &config_path)?;

    let config = Arc::new(RwLock::new(config));

    let registry = new_registry(config.clone());

    let handle = spawn_chain_handle(|| {}, &registry, &node)?;

    let foreign_client = bootstrap_foreign_client(&handle, &handle)?;

    Ok(ConnectedChains::new(
        config_path,
        config,
        registry,
        handle.clone(),
        handle,
        MonoTagged::new(node.clone()),
        MonoTagged::new(node),
        foreign_client.clone(),
        foreign_client,
    ))
}

pub fn pad_client_ids<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain_a: &ChainA,
    chain_b: &ChainB,
) -> Result<(), Error> {
    let foreign_client =
        ForeignClient::restore(ClientId::default(), chain_b.clone(), chain_a.clone());

    for i in 0..random_u64_range(1, 6) {
        debug!("creating new client id {} on chain {}", i + 1, chain_b.id());
        foreign_client.build_create_client_and_send(&Default::default())?;
    }

    Ok(())
}

/**
   Bootstrap a foreign client from `ChainA` to `ChainB`, i.e. the foreign
   client collects information from `ChainA` and submits them as transactions
   to `ChainB`.

   The returned `ForeignClient` is tagged in contravariant position, i.e.
   `ChainB` then `ChainB`, because `ForeignClient` takes the the destination
   chain in the first position.
*/
pub fn bootstrap_foreign_client<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain_a: &ChainA,
    chain_b: &ChainB,
) -> Result<ForeignClient<ChainB, ChainA>, Error> {
    let foreign_client =
        ForeignClient::restore(ClientId::default(), chain_b.clone(), chain_a.clone());

    let event = foreign_client.build_create_client_and_send(&Default::default())?;
    let client_id = extract_client_id(&event)?.clone();

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

/**
   Spawn a new chain handle using the given [`SharedRegistry`] and
   [`FullNode`].

   The function accepts a proxy type `Seed` that should be unique
   accross multiple calls so that the returned [`ChainHandle`]
   have a unique type.

   For example, the following test should fail to compile:

   ```rust,compile_fail
   # use ibc_integration_test::bootstrap::binary::chain::spawn_chain_handle;
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
    chain.add_key(wallet.id.0.clone(), wallet.key.clone())?;

    Ok(())
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
   Create a new [`SharedRegistry`] that uses [`ProdChainHandle`]
   as the [`ChainHandle`] implementation.
*/
pub fn new_registry(config: SharedConfig) -> SharedRegistry<ProdChainHandle> {
    <SharedRegistry<ProdChainHandle>>::new(config)
}

/**
   Generate [`ChainConfig`](ibc_relayer::config::ChainConfig) from a running
   [`FullNode`] and add it to the relayer's [`Config`].
*/
pub fn add_chain_config(config: &mut Config, running_node: &FullNode) -> Result<(), Error> {
    let chain_config = running_node.generate_chain_config()?;

    config.chains.push(chain_config);
    Ok(())
}

/**
   Save a relayer's [`Config`] to the filesystem to make it accessible
   through external CLI.

   Note that the saved config file will not be updated if the
   [`SharedConfig`] is reloaded within the test. So test authors that
   test on the config reloading functionality of the relayer would have to
   call this function again to save the updated relayer config to the
   filesystem.
*/
pub fn save_relayer_config(config: &Config, config_path: &Path) -> Result<(), Error> {
    let config_str = toml::to_string_pretty(&config)?;

    fs::write(&config_path, &config_str)?;

    info!(
        "written hermes config.toml to {}:\n{}",
        config_path.display(),
        config_str
    );

    Ok(())
}
