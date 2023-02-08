//! Various utilities for the Hermes CLI

use alloc::sync::Arc;
use eyre::eyre;
use ibc_relayer_framework::base::relay::types::two_way::TwoWayRelayContext;
use ibc_relayer_framework::full::relay::impls::auto_relayers::parallel_two_way::ParallelTwoWayAutoRelay;
use opentelemetry::global;
use std::collections::HashMap;
use tokio::runtime::Runtime as TokioRuntime;
use tracing::debug;

use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::chain::counterparty::{channel_connection_client, ChannelConnectionClient};
use ibc_relayer::chain::handle::{BaseChainHandle, ChainHandle};
use ibc_relayer::chain::requests::{
    IncludeProof, QueryChannelRequest, QueryClientStateRequest, QueryConnectionRequest, QueryHeight,
};
use ibc_relayer::config::filter::PacketFilter;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::keyring::AnySigningKeyPair;
use ibc_relayer::{config::Config, spawn};
use ibc_relayer_cosmos::contexts::full::chain::FullCosmosChainContext;
use ibc_relayer_cosmos::contexts::full::relay::new_relay_context_with_batch;
use ibc_relayer_cosmos::full::all_for_one::birelay::AfoCosmosFullBiRelay;
use ibc_relayer_cosmos::full::types::telemetry::{CosmosTelemetry, TelemetryState};
use ibc_relayer_framework::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_framework::full::one_for_all::types::telemetry::OfaTelemetryWrapper;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_types::core::ics02_client::client_state::ClientState;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ChannelId, ClientId, PortId};
use ibc_relayer_types::signer::Signer;

use crate::error::Error;

#[derive(Clone, Debug)]
/// Pair of chain handles that are used by most CLIs.
pub struct ChainHandlePair<Chain: ChainHandle = BaseChainHandle> {
    /// Source chain handle
    pub src: Chain,
    /// Destination chain handle
    pub dst: Chain,
}

impl<Chain: ChainHandle> ChainHandlePair<Chain> {
    /// Spawn the source and destination chain runtime from the configuration and chain identifiers,
    /// and return the pair of associated handles.
    pub fn spawn_generic(
        config: &Config,
        src_chain_id: &ChainId,
        dst_chain_id: &ChainId,
    ) -> Result<Self, Error> {
        let src = spawn_chain_runtime_generic(config, src_chain_id)?;
        let dst = spawn_chain_runtime_generic(config, dst_chain_id)?;

        Ok(ChainHandlePair { src, dst })
    }
}

impl ChainHandlePair<BaseChainHandle> {
    pub fn spawn(
        config: &Config,
        src_chain_id: &ChainId,
        dst_chain_id: &ChainId,
    ) -> Result<Self, Error> {
        Self::spawn_generic(config, src_chain_id, dst_chain_id)
    }
}

/// Spawns a chain runtime for the chain in the configuration identified by given a chain identifier.
///
/// This function will use the default [`ChainHandle`] implementation, ie. the [`BaseChainHandle`].
///
/// Returns the corresponding handle if successful.
pub fn spawn_chain_runtime(config: &Config, chain_id: &ChainId) -> Result<impl ChainHandle, Error> {
    spawn_chain_runtime_generic::<BaseChainHandle>(config, chain_id)
}

/// Spawns a chain runtime for the chain in the configuraiton identified by the given chain identifier.
///
/// The `Handle` type parameter allows choosing which kind of [`ChainHandle`] implementation to use.
///
/// Returns the corresponding handle if successful.
pub fn spawn_chain_runtime_generic<Handle: ChainHandle>(
    config: &Config,
    chain_id: &ChainId,
) -> Result<Handle, Error> {
    let rt = Arc::new(TokioRuntime::new().unwrap());
    spawn::spawn_chain_runtime(config, chain_id, rt).map_err(Error::spawn)
}

/// Spawns a chain runtime for specified chain identifier, queries the counterparty chain associated
/// with specified port and channel id, and spawns a chain runtime for the counterparty chain.
///
/// The `Handle` type parameter allows choosing which kind of `ChainHandle` implementation to use.
///
/// Returns a tuple with a pair of associated chain handles and the ChannelEnd
pub fn spawn_chain_counterparty<Chain: ChainHandle>(
    config: &Config,
    chain_id: &ChainId,
    port_id: &PortId,
    channel_id: &ChannelId,
) -> Result<(ChainHandlePair<Chain>, ChannelConnectionClient), Error> {
    let chain = spawn_chain_runtime_generic::<Chain>(config, chain_id)?;
    let channel_connection_client =
        channel_connection_client(&chain, port_id, channel_id).map_err(Error::supervisor)?;
    let counterparty_chain = {
        let counterparty_chain_id = channel_connection_client.client.client_state.chain_id();
        spawn_chain_runtime_generic::<Chain>(config, &counterparty_chain_id)?
    };

    Ok((
        ChainHandlePair {
            src: chain,
            dst: counterparty_chain,
        },
        channel_connection_client,
    ))
}

/// Check that the relayer can send on the given channel and ensure that channels and chain identifiers match.
/// To do this, fetch from the source chain the channel end, then the associated connection
/// end, and then the underlying client state; finally, check that this client is verifying
/// headers for the destination chain.
pub fn check_can_send_on_channel<Chain: ChainHandle>(
    src_chain: &Chain,
    src_channel_id: &ChannelId,
    src_port_id: &PortId,
    dst_chain_id: &ChainId,
) -> Result<(), eyre::Report> {
    // Fetch from the source chain the channel end and check that it is open.
    let (channel_end_src, _) = src_chain.query_channel(
        QueryChannelRequest {
            port_id: src_port_id.clone(),
            channel_id: src_channel_id.clone(),
            height: QueryHeight::Latest,
        },
        IncludeProof::No,
    )?;

    if !channel_end_src.is_open() {
        return Err(eyre!(
            "the requested port/channel ('{}'/'{}') on chain id '{}' is in state '{}'; expected 'open' state",
            src_port_id,
            src_channel_id,
            src_chain.id(),
            channel_end_src.state
        ));
    }

    let conn_id = match channel_end_src.connection_hops.first() {
        Some(cid) => cid,
        None => {
            return Err(eyre!(
                "could not retrieve the connection hop underlying port/channel '{}'/'{}' on chain '{}'",
                src_port_id, src_channel_id, src_chain.id()
            ));
        }
    };

    // Fetch the associated connection end.
    let (conn_end, _) = src_chain.query_connection(
        QueryConnectionRequest {
            connection_id: conn_id.clone(),
            height: QueryHeight::Latest,
        },
        IncludeProof::No,
    )?;

    debug!("connection hop underlying the channel: {:?}", conn_end);

    // Fetch the underlying client state.
    let (src_chain_client_state, _) = src_chain.query_client_state(
        QueryClientStateRequest {
            client_id: conn_end.client_id().clone(),
            height: QueryHeight::Latest,
        },
        IncludeProof::No,
    )?;

    debug!(
        "client state underlying the channel: {:?}",
        src_chain_client_state
    );

    // Check that this client is verifying headers for the destination chain.
    if &src_chain_client_state.chain_id() != dst_chain_id {
        return Err(eyre!(
            "the requested port/channel ('{}'/'{}') provides a path from chain '{}' to \
             chain '{}' (not to the destination chain '{}'). Bailing due to mismatching arguments.",
            src_port_id,
            src_channel_id,
            src_chain.id(),
            src_chain_client_state.chain_id(),
            dst_chain_id
        ));
    }

    Ok(())
}

// #[cfg(feature = "relayer-next")]
pub fn build_cosmos_birelay_context<ChainA, ChainB>(
    handle_a: ChainA,
    handle_b: ChainB,
    client_id_a: ClientId,
    client_id_b: ClientId,
    runtime: TokioRuntime,
    filter: PacketFilter,
) -> Result<impl AfoCosmosFullBiRelay, Error>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    let telemetry = OfaTelemetryWrapper::new(CosmosTelemetry::new(TelemetryState {
        meter: global::meter("hermes"),
        counters: HashMap::new(),
        value_recorders: HashMap::new(),
        updown_counters: HashMap::new(),
    }));

    let runtime = OfaRuntimeWrapper::new(TokioRuntimeContext::new(Arc::new(runtime)));

    let chain_a_signer = handle_a.get_signer().unwrap_or_else(|_| Signer::dummy());
    let chain_b_signer = handle_b.get_signer().unwrap_or_else(|_| Signer::dummy());

    let Ok(AnySigningKeyPair::Secp256k1(chain_a_key)) =handle_a.get_key() else {
        panic!("No Secp256k1 key pair for chain {}", handle_a.id());
    };

    let Ok(AnySigningKeyPair::Secp256k1(chain_b_key)) = handle_b.get_key() else {
        panic!("No Secp256k1 key pair for chain {}", handle_b.id());
    };

    let chain_a_config = handle_a.config().unwrap();
    let chain_a_websocket_addr = chain_a_config.websocket_addr.clone();
    let chain_a_config = TxConfig::try_from(&chain_a_config).unwrap();

    let chain_b_config = handle_b.config().unwrap();
    let chain_b_websocket_addr = chain_b_config.websocket_addr.clone();
    let chain_b_config = TxConfig::try_from(&chain_b_config).unwrap();

    let chain_a = FullCosmosChainContext::new(
        handle_a.clone(),
        chain_a_signer,
        chain_a_config,
        chain_a_websocket_addr,
        chain_a_key,
        telemetry.clone(),
    );
    let chain_b = FullCosmosChainContext::new(
        handle_b.clone(),
        chain_b_signer,
        chain_b_config,
        chain_b_websocket_addr,
        chain_b_key,
        telemetry,
    );

    let client_a_to_b = ForeignClient::restore(client_id_b, handle_b.clone(), handle_a.clone());
    let client_b_to_a = ForeignClient::restore(client_id_a, handle_a, handle_b);

    let relay_a_to_b = new_relay_context_with_batch(
        runtime.clone(),
        chain_a.clone(),
        chain_b.clone(),
        client_a_to_b.clone(),
        client_b_to_a.clone(),
        filter.clone(),
        Default::default(),
    );

    let relay_b_to_a = new_relay_context_with_batch(
        runtime,
        chain_b,
        chain_a,
        client_b_to_a,
        client_a_to_b,
        filter,
        Default::default(),
    );

    let birelay = TwoWayRelayContext::new(ParallelTwoWayAutoRelay, relay_a_to_b, relay_b_to_a);

    Ok(birelay)
}
