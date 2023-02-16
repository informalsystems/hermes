use alloc::sync::Arc;
use opentelemetry::global;
use std::collections::HashMap;
use tokio::runtime::Runtime as TokioRuntime;

use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::config::filter::PacketFilter;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::keyring::AnySigningKeyPair;
use ibc_relayer_cosmos::contexts::full::chain::FullCosmosChainContext;
use ibc_relayer_cosmos::contexts::full::relay::new_relay_context_with_batch;
use ibc_relayer_cosmos::full::all_for_one::birelay::AfoCosmosFullBiRelay;
use ibc_relayer_cosmos::full::types::telemetry::{CosmosTelemetry, TelemetryState};
use ibc_relayer_framework::base::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_framework::base::relay::types::two_way::TwoWayRelayContext;
use ibc_relayer_framework::full::one_for_all::types::telemetry::OfaTelemetryWrapper;
use ibc_relayer_framework::full::relay::impls::auto_relayers::parallel_two_way::ParallelTwoWayAutoRelay;
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_types::core::ics24_host::identifier::ClientId;

use crate::error::Error;

/// Initializes a Cosmos relay context that utilizes the experimental relayer
/// architecture for relaying packets between two Cosmos chains.
#[cfg(feature = "experimental")]
pub fn build_cosmos_birelay_context<ChainA, ChainB>(
    handle_a: ChainA,
    handle_b: ChainB,
    client_id_a: ClientId,
    client_id_b: ClientId,
    runtime: Arc<TokioRuntime>,
    filter: PacketFilter,
) -> Result<impl AfoCosmosFullBiRelay, Error>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
{
    use ibc_relayer_cosmos::base::types::chain::CosmosChainWrapper;
    use ibc_relayer_framework::base::one_for_all::types::chain::OfaChainWrapper;

    let telemetry = OfaTelemetryWrapper::new(CosmosTelemetry::new(TelemetryState {
        meter: global::meter("hermes"),
        counters: HashMap::new(),
        value_recorders: HashMap::new(),
        updown_counters: HashMap::new(),
    }));

    let runtime = OfaRuntimeWrapper::new(TokioRuntimeContext::new(runtime));

    let chain_a_signer = handle_a.get_signer().map_err(Error::relayer)?;
    let chain_b_signer = handle_b.get_signer().map_err(Error::relayer)?;

    let chain_a_keypair = handle_a.get_key().map_err(Error::relayer)?;
    let chain_b_keypair = handle_b.get_key().map_err(Error::relayer)?;

    let AnySigningKeyPair::Secp256k1(chain_a_key) = chain_a_keypair else {
        return Err(Error::secp256k1_key_pair(handle_a.id()));
    };

    let AnySigningKeyPair::Secp256k1(chain_b_key) = chain_b_keypair else {
        return Err(Error::secp256k1_key_pair(handle_b.id()));
    };

    let chain_a_config = handle_a.config().map_err(Error::relayer)?;
    let chain_a_websocket_addr = chain_a_config.websocket_addr.clone();
    let chain_a_config = TxConfig::try_from(&chain_a_config).map_err(Error::relayer)?;

    let chain_b_config = handle_b.config().map_err(Error::relayer)?;
    let chain_b_websocket_addr = chain_b_config.websocket_addr.clone();
    let chain_b_config = TxConfig::try_from(&chain_b_config).map_err(Error::relayer)?;

    let chain_a = OfaChainWrapper::new(CosmosChainWrapper::new(Arc::new(
        FullCosmosChainContext::new(
            handle_a.clone(),
            chain_a_signer,
            chain_a_config,
            chain_a_websocket_addr,
            chain_a_key,
            runtime.clone(),
            telemetry.clone(),
        ),
    )));

    let chain_b = OfaChainWrapper::new(CosmosChainWrapper::new(Arc::new(
        FullCosmosChainContext::new(
            handle_b.clone(),
            chain_b_signer,
            chain_b_config,
            chain_b_websocket_addr,
            chain_b_key,
            runtime.clone(),
            telemetry,
        ),
    )));

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
