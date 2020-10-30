//! Task for initializing and spawning a light client for a given chain

use std::time::Duration;

use abscissa_core::{
    error::BoxError,
    tracing::{debug, info},
};

use futures::Future;
use tendermint::chain;
use tendermint_light_client::{
    builder::{LightClientBuilder, SupervisorBuilder},
    light_client, store,
    supervisor::{self, Handle, Supervisor, SupervisorHandle},
    types::PeerId,
};

use relayer::{
    chain::{Chain, CosmosSDKChain},
    client::{self, TrustOptions},
};

use crate::prelude::*;

/// Initialize a light client for a given chain.
///
/// This function returns an async task which can be spawned
/// to start the light client and have it sync up to the latest
/// block of the chain.
///
/// If the `reset` parameter is set to `true`, then the
/// light client will be initialized with the given trust options,
/// otherwise it will resume from the latest trusted block in the store.
pub async fn create(
    chain: &mut CosmosSDKChain,
    trust_options: TrustOptions,
    reset: bool,
) -> Result<impl Future<Output = Result<(), BoxError>>, BoxError> {
    status_info!(
        "Relayer",
        "spawning light client for chain {}",
        chain.config().id,
    );

    let supervisor = create_client(chain, trust_options, reset).await?;
    let handle = supervisor.handle();
    let thread_handle = std::thread::spawn(|| supervisor.run());
    let task = client_task(chain.id().clone(), handle.clone());

    let light_client = client::tendermint::LightClient::new(handle);
    chain.set_light_client(light_client);

    Ok(task)
}

fn build_instance(
    peer_id: PeerId,
    chain: &CosmosSDKChain,
    store: store::sled::SledStore,
    options: light_client::Options,
    trust_options: TrustOptions,
    reset: bool,
) -> Result<supervisor::Instance, BoxError> {
    let builder = LightClientBuilder::prod(
        peer_id,
        chain.rpc_client().clone(),
        Box::new(store),
        options,
        Some(Duration::from_secs(10)), // TODO: Make configurable
    );

    let builder = if reset {
        info!(chain.id = %chain.id(), "resetting client to trust options state");
        builder.trust_primary_at(trust_options.height, trust_options.header_hash)?
    } else {
        info!(chain.id = %chain.id(), "starting client from stored trusted state");
        builder.trust_from_store()?
    };

    Ok(builder.build())
}

async fn create_client(
    chain: &mut CosmosSDKChain,
    trust_options: TrustOptions,
    reset: bool,
) -> Result<Supervisor, BoxError> {
    let chain_config = chain.config();
    let id = chain_config.id.clone();

    let db_path = format!("store_{}.db", chain.id());
    let store = store::sled::SledStore::new(sled::open(db_path)?);

    // FIXME: Remove or make configurable
    let primary_peer_id: PeerId = "BADFADAD0BEFEEDC0C0ADEADBEEFC0FFEEFACADE".parse().unwrap();
    let witness_peer_id: PeerId = "DC0C0ADEADBEEFC0FFEEFACADEBADFADAD0BEFEE".parse().unwrap();

    let options = light_client::Options {
        trust_threshold: trust_options.trust_threshold,
        trusting_period: trust_options.trusting_period,
        clock_drift: Duration::from_secs(5), // TODO: Make configurable
    };

    let primary = build_instance(
        primary_peer_id,
        &chain,
        store.clone(),
        options,
        trust_options.clone(),
        reset,
    )?;

    let witness = build_instance(
        witness_peer_id,
        &chain,
        store,
        options,
        trust_options,
        reset,
    )?;

    let supervisor = SupervisorBuilder::new()
        .primary(primary_peer_id, chain_config.rpc_addr.clone(), primary)
        .witness(witness_peer_id, chain_config.rpc_addr.clone(), witness)
        .build_prod();

    Ok(supervisor)
}

async fn client_task(chain_id: chain::Id, handle: SupervisorHandle) -> Result<(), BoxError> {
    match handle.latest_trusted() {
        Ok(Some(trusted_state)) => {
            info!(
                chain.id = %chain_id,
                "spawned new client now at trusted state: {} at height {}",
                trusted_state.signed_header.header().hash(),
                trusted_state.signed_header.header().height,
            );

            update_client(chain_id, handle).await?;
        }
        Ok(None) => {
            error!(
                chain.id = %chain_id,
                "no initial trusted state, aborting"
            );
        }
        Err(e) => {
            error!(
                chain.id = %chain_id,
                "error getting latest trusted state: {}", e
            );
        }
    }

    Ok(())
}

async fn update_client(chain_id: chain::Id, handle0: SupervisorHandle) -> Result<(), BoxError> {
    debug!(chain.id = %chain_id, "updating headers");

    let mut interval = tokio::time::interval(Duration::from_secs(3));

    loop {
        interval.tick().await;

        info!(chain.id = %chain_id, "updating client");

        let handle = handle0.clone();
        let result = tokio::task::spawn_blocking(move || handle.verify_to_highest()).await?;

        match result {
            Ok(trusted_state) => info!(
                chain.id = %chain_id,
                "client updated to trusted state: {} at height {}",
                trusted_state.signed_header.header().hash(),
                trusted_state.signed_header.header().height
            ),

            Err(err) => error!(chain.id = %chain_id, "error when updating headers: {}", err),
        }
    }
}
