use ibc_relayer_types::clients::ics07_tendermint::client_state::ClientState;
use tendermint::{
    evidence::{
        Evidence,
        LightClientAttackEvidence,
    },
    Hash,
    Time,
};
use tendermint_light_client::{
    builder::LightClientBuilder,
    components::{
        clock::FixedClock,
        io::ProdIo,
        scheduler,
    },
    predicates::ProdPredicates,
    store::memory::MemoryStore,
    types::{
        LightBlock,
        PeerId,
    },
    verifier::ProdVerifier,
};
use tendermint_light_client_detector::{
    detect_divergence,
    Divergence,
    Provider,
};
use tendermint_rpc::{
    Client,
    HttpClient,
};
use tracing::{
    error,
    info,
};

use crate::{
    error::Error,
    util::block_on,
};

type Hasher = tendermint::crypto::default::Sha256;

pub fn detect(
    peer_id: PeerId,
    rpc_client: HttpClient,
    target_block: LightBlock,
    trusted_block: LightBlock,
    client_state: &ClientState,
    now: Time,
) -> Result<Option<Divergence>, Error> {
    let primary_trace = vec![trusted_block.clone(), target_block];
    let options = client_state.as_light_client_options();
    let mut provider = make_provider(peer_id, rpc_client, client_state, trusted_block, now)?;

    let divergence = block_on(detect_divergence::<Hasher>(
        None,
        &mut provider,
        primary_trace,
        options.clock_drift,
        options.trusting_period,
    ));

    match divergence {
        Ok(None) => {
            info!(
                "No evidence of misbehavior detected for chain {}",
                client_state.chain_id
            );

            Ok(None)
        }
        Ok(Some(divergence)) => {
            info!(
                "Evidence of misbehavior detected for chain {}",
                client_state.chain_id
            );

            Ok(Some(divergence))
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
    now: Time,
) -> Result<Provider, Error> {
    let options = client_state.as_light_client_options();
    let light_store = Box::new(MemoryStore::new());

    let builder = LightClientBuilder::custom(
        peer_id,
        options,
        light_store,
        Box::new(ProdIo::new(peer_id, rpc_client.clone(), None)),
        Box::new(FixedClock::new(now)),
        Box::<ProdVerifier>::default(),
        Box::new(scheduler::basic_bisecting_schedule),
        Box::new(ProdPredicates),
    );

    let instance = builder
        .trust_light_block(trusted_block)
        .map_err(Error::light_client_builder)?
        .build();

    Ok(Provider::new(
        client_state.chain_id.to_string(),
        instance,
        rpc_client,
    ))
}

pub fn report_evidence(
    rpc_client: HttpClient,
    attack: LightClientAttackEvidence,
) -> Result<Hash, Error> {
    block_on(rpc_client.broadcast_evidence(Evidence::from(attack)))
        .map(|response| response.hash)
        .map_err(|e| Error::rpc_response(e.to_string()))
}
