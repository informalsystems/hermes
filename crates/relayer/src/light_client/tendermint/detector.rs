use ibc_relayer_types::{
    clients::ics07_tendermint::client_state::ClientState, core::ics24_host::identifier::ChainId,
    Height,
};
use tendermint::{evidence::LightClientAttackEvidence, hash::Hash, Time};
use tendermint_light_client::{
    builder::LightClientBuilder,
    light_client::Options,
    misbehavior::{detect_divergence, Provider},
    store::{memory::MemoryStore, LightStore},
    types::{LightBlock, PeerId, Status},
};
use tendermint_rpc::{Client, HttpClient};
use tracing::{error, info};

use crate::{error::Error, util::block_on};

pub fn detect(
    peer_id: PeerId,
    rpc_client: HttpClient,
    target_block: LightBlock,
    trusted_block: LightBlock,
    client_state: &ClientState,
    now: Time,
) -> Result<Option<LightClientAttackEvidence>, Error> {
    let primary_trace = vec![trusted_block.clone(), target_block];
    let options = client_state.as_light_client_options();
    let mut provider = make_provider(peer_id, rpc_client, client_state, trusted_block)?;

    let evidence = block_on(detect_divergence(
        &mut provider,
        primary_trace,
        options.clock_drift,
        options.trusting_period,
        now,
    ));

    match evidence {
        Ok(None) => {
            info!(
                "No evidence of misbehavior detected for chain {}",
                client_state.chain_id
            );

            Ok(None)
        }
        Ok(Some(evidence)) => {
            info!(
                "Evidence of misbehavior detected for chain {}",
                client_state.chain_id
            );

            Ok(Some(evidence))
        }
        Err(e) => {
            error!(
                "Error while detecting misbehavior for chain {}: {}",
                client_state.chain_id, e
            );

            Ok(None)
        }
    }
}

fn make_provider(
    peer_id: PeerId,
    rpc_client: HttpClient,
    client_state: &ClientState,
    trusted_block: LightBlock,
) -> Result<Provider, Error> {
    let mut light_store = Box::new(MemoryStore::new());
    light_store.insert(trusted_block, Status::Trusted);

    let options = client_state.as_light_client_options();

    let instance =
        LightClientBuilder::prod(peer_id, rpc_client.clone(), light_store, options, None)
            .trust_from_store()
            .map_err(Error::light_client_builder)?
            .build();

    Ok(Provider::new(
        client_state.chain_id.to_string(),
        instance,
        rpc_client,
    ))
}
