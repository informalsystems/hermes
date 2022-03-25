/*!
    Helper functions for bootstrapping two relayer chain handles
    with connected foreign clients.
*/

use eyre::Report as Error;
use ibc::core::ics24_host::identifier::ClientId;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::Config;
use ibc_relayer::foreign_client::{extract_client_id, ForeignClient};
use std::sync::{Arc, RwLock};
use tracing::{debug, info};

use crate::relayer::driver::RelayerDriver;
use crate::relayer::spawn::{
    add_chain_config, new_registry, save_relayer_config, spawn_chain_handle,
};
use crate::types::binary::chains::ConnectedChains;
use crate::types::binary::foreign_client::ForeignClientPair;
use crate::types::config::TestConfig;
use crate::types::single::node::FullNode;
use crate::types::tagged::*;
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

    let foreign_clients = bootstrap_foreign_client_pair(&handle_a, &handle_b)?;

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
) -> Result<
    (
        RelayerDriver,
        ConnectedChains<impl ChainHandle, impl ChainHandle>,
    ),
    Error,
> {
    boostrap_chain_pair_with_nodes(test_config, node.clone(), node, config_modifier)
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

pub fn bootstrap_foreign_client_pair<ChainA: ChainHandle, ChainB: ChainHandle>(
    chain_a: &ChainA,
    chain_b: &ChainB,
) -> Result<ForeignClientPair<ChainA, ChainB>, Error> {
    let client_a_to_b = bootstrap_foreign_client(chain_a, chain_b)?;
    let client_b_to_a = bootstrap_foreign_client(chain_b, chain_a)?;

    Ok(ForeignClientPair::new(client_a_to_b, client_b_to_a))
}

/**
   Bootstrap a foreign client from `ChainA` to `ChainB`, i.e. the foreign
   client collects information from `ChainA` and submits them as transactions
   to `ChainB`.

   The returned `ForeignClient` is tagged in contravariant ordering, i.e.
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
