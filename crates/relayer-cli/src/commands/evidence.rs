use std::collections::HashMap;
use std::ops::Deref;
use std::sync::Arc;
use std::thread::sleep;
use std::time::Duration;

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use tokio::runtime::Runtime as TokioRuntime;

use tendermint::block::Height as TendermintHeight;
use tendermint::evidence::{DuplicateVoteEvidence, LightClientAttackEvidence};
use tendermint::validator;
use tendermint_rpc::{Client, Paging};

use ibc_relayer::chain::cosmos::CosmosSdkChain;
use ibc_relayer::chain::endpoint::ChainEndpoint;
use ibc_relayer::chain::handle::{BaseChainHandle, ChainHandle};
use ibc_relayer::chain::requests::{IncludeProof, PageRequest, QueryHeight};
use ibc_relayer::chain::tracking::TrackedMsgs;
use ibc_relayer::chain::ChainType;
use ibc_relayer::foreign_client::ForeignClient;
use ibc_relayer::spawn::spawn_chain_runtime_with_modified_config;
use ibc_relayer_types::applications::ics28_ccv::msgs::ccv_double_voting::MsgSubmitIcsConsumerDoubleVoting;
use ibc_relayer_types::applications::ics28_ccv::msgs::ccv_misbehaviour::MsgSubmitIcsConsumerMisbehaviour;
use ibc_relayer_types::clients::ics07_tendermint::header::Header as TendermintHeader;
use ibc_relayer_types::clients::ics07_tendermint::misbehaviour::Misbehaviour as TendermintMisbehaviour;
use ibc_relayer_types::core::ics02_client::client_state::ClientState;
use ibc_relayer_types::core::ics02_client::height::Height;
use ibc_relayer_types::core::ics02_client::msgs::misbehaviour::MsgSubmitMisbehaviour;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId};
use ibc_relayer_types::events::IbcEvent;
use ibc_relayer_types::tx_msg::Msg;

use crate::conclude::Output;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct EvidenceCmd {
    #[clap(
        long = "chain",
        required = true,
        value_name = "CHAIN_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the chain where blocks are monitored for misbehaviour"
    )]
    chain_id: ChainId,

    #[clap(
        long = "check-past-blocks",
        value_name = "NUM_BLOCKS",
        help = "Check the last NUM_BLOCKS blocks for misbehaviour (default: 100)",
        default_value = "100"
    )]
    check_past_blocks: u64,

    #[clap(
        long = "key-name",
        value_name = "KEY_NAME",
        help = "Use the given signing key name for sending the misbehaviour evidence detected (default: `key_name` config)"
    )]
    key_name: Option<String>,
}

impl Runnable for EvidenceCmd {
    fn run(&self) {
        let config = app_config();

        let mut chain_config = config
            .find_chain(&self.chain_id)
            .cloned()
            .unwrap_or_else(|| {
                Output::error(format!(
                    "chain '{}' not found in configuration",
                    self.chain_id
                ))
                .exit()
            });

        if chain_config.r#type != ChainType::CosmosSdk {
            Output::error(format!("Chain {} is not a Cosmos SDK chain", self.chain_id)).exit();
        }

        if let Some(ref key_name) = self.key_name {
            chain_config.key_name = key_name.to_string();
        }

        let rt = Arc::new(
            tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()
                .unwrap(),
        );

        let chain = CosmosSdkChain::bootstrap(chain_config, rt.clone()).unwrap();
        let res = monitor_misbehaviours(rt, chain, self.key_name.as_ref(), self.check_past_blocks);

        match res {
            Ok(()) => Output::success(()).exit(),
            Err(e) => Output::error(e).exit(),
        }
    }
}

fn monitor_misbehaviours(
    rt: Arc<TokioRuntime>,
    mut chain: CosmosSdkChain,
    key_name: Option<&String>,
    check_past_blocks: u64,
) -> eyre::Result<()> {
    let subscription = chain.subscribe()?;

    // Check previous blocks for equivocation that may have been missed
    let tm_latest_height = rt
        .block_on(chain.rpc_client.status())?
        .sync_info
        .latest_block_height;

    let latest_height = Height::new(chain.id().version(), tm_latest_height.value()).unwrap();
    let target_height = {
        let target = tm_latest_height.value().saturating_sub(check_past_blocks);
        let height = std::cmp::max(1, target);
        Height::new(chain.id().version(), height).unwrap()
    };

    // latest_height: 200
    //
    // check_past_blocks: 0
    // target_height: 200
    // iterations: 0
    //
    // check_past_blocks: 1
    // target_height: 199
    // iterations: 1
    //
    // check_past_blocks: 200
    // target_height: 1
    // iterations: 200
    //
    // check_past_blocks: 201
    // target_height: 1
    // iterations: 200

    info!(
        "checking past {check_past_blocks} blocks for misbehaviour evidence: {}..{}",
        latest_height, target_height
    );

    let mut height = latest_height;

    while height >= target_height {
        debug!("checking for evidence at height {height}");

        if let Err(e) = check_misbehaviour_at(rt.clone(), &chain, key_name, height) {
            warn!("error while checking for misbehaviour at height {height}: {e}");
        }

        if height.revision_height() == 1 {
            break;
        }

        height = height.decrement().unwrap();

        sleep(Duration::from_millis(100));
    }

    info!("waiting for new blocks...");

    // process new block events
    while let Ok(event_batch) = subscription.recv() {
        match event_batch.deref() {
            Ok(event_batch) => {
                for event_with_height in &event_batch.events {
                    if let IbcEvent::NewBlock(new_block) = &event_with_height.event {
                        info!("checking for evidence at height {}", new_block.height);

                        if let Err(e) =
                            check_misbehaviour_at(rt.clone(), &chain, key_name, new_block.height)
                        {
                            error!(
                                "error while checking for misbehaviour at height {}: {e}",
                                new_block.height
                            );
                        }
                    }
                }
            }
            Err(e) => {
                error!("error while receiving event batch: {e}");
            }
        }
    }

    Ok(())
}

/// Check for misbehaviour evidence in the block at the given height.
/// If such evidence is found, handle it by submitting it to all counterparty
/// clients of the chain, freezing them.
fn check_misbehaviour_at(
    rt: Arc<TokioRuntime>,
    chain: &CosmosSdkChain,
    key_name: Option<&String>,
    height: Height,
) -> eyre::Result<()> {
    let block = rt
        .block_on(chain.rpc_client.block(TendermintHeight::from(height)))?
        .block;

    for evidence in block.evidence.into_vec() {
        match evidence {
            tendermint::evidence::Evidence::DuplicateVote(dv) => {
                warn!("found duplicate vote evidence");
                trace!("{dv:#?}");

                handle_duplicate_vote(rt.clone(), chain, key_name, *dv)?;
            }
            tendermint::evidence::Evidence::LightClientAttack(lc) => {
                warn!("found light client attack evidence");
                trace!("{lc:#?}");

                handle_light_client_attack(rt.clone(), chain, key_name, *lc)?;
            }
        }
    }

    Ok(())
}

fn handle_duplicate_vote(
    rt: Arc<TokioRuntime>,
    chain: &CosmosSdkChain,
    key_name: Option<&String>,
    dv: DuplicateVoteEvidence,
) -> eyre::Result<()> {
    use ibc_relayer::chain::requests::QueryConsensusStateHeightsRequest;

    let config = app_config();

    // Fetch all the counterparty clients of this chain.
    let counterparty_clients = fetch_all_counterparty_clients(chain)?;

    let mut chains = HashMap::new();

    // For each counterparty client, build the double voting evidence and submit it to the chain,
    // freezing that client.
    for (counterparty_chain_id, counterparty_client_id) in counterparty_clients {
        if !chains.contains_key(&counterparty_chain_id) {
            let chain_handle = spawn_chain_runtime_with_modified_config::<BaseChainHandle>(
                &config,
                &counterparty_chain_id,
                rt.clone(),
                |chain_config| {
                    if let Some(key_name) = key_name {
                        chain_config.key_name = key_name.to_string();
                    }
                },
            )?;

            chains.insert(counterparty_chain_id.clone(), chain_handle);
        };

        let counterparty_chain_handle = chains.get(&counterparty_chain_id).unwrap();

        let signer = counterparty_chain_handle.get_signer()?;

        // If the misbehaving chain is a CCV consumer chain,
        // then try fetch the consumer chains of the counterparty chains.
        // If that fails, then that chain is not a provider chain.
        // Otherwise, check if the misbehaving chain is a consumer of the counterparty chain,
        // which is definitely a provider.
        let counterparty_is_provider = if chain.config().ccv_consumer_chain {
            let consumer_chains = counterparty_chain_handle
                .query_consumer_chains()
                .unwrap_or_default(); // If the query fails, use an empty list of consumers

            // FIXME: Do do we need to check if the client id also matches?
            // ie. is it okay to submit a `MsgSubmitIcsConsumerDoubleVoting` to all clients
            // of the provider chain, or should we only do this for the CCV client, and
            // use the standard message for other clients?
            consumer_chains
                .iter()
                .any(|(chain_id, _)| chain_id == chain.id())
        } else {
            false
        };

        if !counterparty_is_provider {
            debug!("counterparty chain {counterparty_chain_id} is not a CCV provider chain, skipping...");
            continue;
        }

        let infraction_height = dv.vote_a.height;

        // Get the trusted height in the same way we do for client updates,
        // ie. retrieve the consensus state at the highest height smaller than the infraction height.
        //
        // Note: The consensus state heights are sorted in increasing order.
        let consensus_state_heights =
            chain.query_consensus_state_heights(QueryConsensusStateHeightsRequest {
                client_id: counterparty_client_id.clone(),
                pagination: Some(PageRequest::all()),
            })?;

        // Retrieve the consensus state at the highest height smaller than the infraction height.
        let consensus_state_height_before_infraction_height = consensus_state_heights
            .into_iter()
            .filter(|height| height.revision_height() < infraction_height.value())
            .last();

        let Some(trusted_height) = consensus_state_height_before_infraction_height else {
            error!(
                "cannot build infraction block header for client {counterparty_client_id} on chain {counterparty_chain_id},\
                reason: could not find consensus state at highest height smaller than infraction height {infraction_height}"
            );

            continue;
        };

        // Construct the light client block header for the consumer chain at the infraction height
        let infraction_block_header =
            fetch_infraction_block_header(&rt, chain, infraction_height, trusted_height)?;

        let submit_msg = MsgSubmitIcsConsumerDoubleVoting {
            submitter: signer.clone(),
            duplicate_vote_evidence: dv.clone(),
            infraction_block_header,
        }
        .to_any();

        info!(
            "submitting consumer double voting evidence to provider chain {counterparty_chain_id}"
        );

        let tracked_msgs = TrackedMsgs::new_static(vec![submit_msg], "double_voting_evidence");
        let responses = counterparty_chain_handle.send_messages_and_wait_check_tx(tracked_msgs)?;

        for response in responses {
            if response.code.is_ok() {
                info!("successfully submitted double voting evidence to chain {counterparty_chain_id}, tx hash: {}", response.hash);
            } else {
                error!(
                    "failed to submit double voting evidence to chain {counterparty_chain_id}: {response:?}"
                );
            }
        }

        // We have submitted the evidence to the provider, and because there can only be a single
        // provider for a consumer chain, we can stop now. No need to check all the other
        // counteparties.
        break;
    }

    Ok(())
}

fn fetch_infraction_block_header(
    rt: &Arc<TokioRuntime>,
    chain: &CosmosSdkChain,
    infraction_height: TendermintHeight,
    trusted_height: Height,
) -> Result<TendermintHeader, eyre::Error> {
    let signed_header = rt
        .block_on(chain.rpc_client.commit(infraction_height))?
        .signed_header;

    let validators = rt
        .block_on(chain.rpc_client.validators(infraction_height, Paging::All))?
        .validators;

    let validator_set =
        validator::Set::with_proposer(validators, signed_header.header.proposer_address)?;

    let trusted_header = rt
        .block_on(chain.rpc_client.commit(trusted_height))?
        .signed_header;

    let trusted_validators = rt
        .block_on(chain.rpc_client.validators(trusted_height, Paging::All))?
        .validators;

    let trusted_validator_set =
        validator::Set::with_proposer(trusted_validators, trusted_header.header.proposer_address)?;

    Ok(TendermintHeader {
        signed_header,
        validator_set,
        trusted_height,
        trusted_validator_set,
    })
}

fn handle_light_client_attack(
    rt: Arc<TokioRuntime>,
    chain: &CosmosSdkChain,
    key_name: Option<&String>,
    evidence: LightClientAttackEvidence,
) -> eyre::Result<()> {
    let config = app_config();

    // Build the two headers to submit as part of the `MsgSubmitMisbehaviour` message.
    let (header1, header2) = build_evidence_headers(rt.clone(), chain, evidence.clone())?;

    // Fetch all the counterparty clients of this chain.
    let counterparty_clients = fetch_all_counterparty_clients(chain)?;

    let mut chains = HashMap::new();

    // For each counterparty client, build the misbehaviour evidence and submit it to the chain,
    // freezing that client.
    for (counterparty_chain_id, counterparty_client_id) in counterparty_clients {
        let misbehaviour = TendermintMisbehaviour {
            client_id: counterparty_client_id.clone(),
            header1: header1.clone(),
            header2: header2.clone(),
        };

        if !chains.contains_key(chain.id()) {
            let chain_handle = spawn_chain_runtime_with_modified_config::<BaseChainHandle>(
                &config,
                chain.id(),
                rt.clone(),
                |chain_config| {
                    if let Some(key_name) = key_name {
                        chain_config.key_name = key_name.to_string();
                    }
                },
            )?;

            chains.insert(chain.id().clone(), chain_handle);
        }

        if !chains.contains_key(&counterparty_chain_id) {
            let chain_handle = spawn_chain_runtime_with_modified_config::<BaseChainHandle>(
                &config,
                &counterparty_chain_id,
                rt.clone(),
                |chain_config| {
                    if let Some(key_name) = key_name {
                        chain_config.key_name = key_name.to_string();
                    }
                },
            )?;

            chains.insert(counterparty_chain_id.clone(), chain_handle);
        };

        let chain_handle = chains.get(chain.id()).unwrap();
        let counterparty_chain_handle = chains.get(&counterparty_chain_id).unwrap();

        let counterparty_client = ForeignClient::restore(
            counterparty_client_id.clone(),
            counterparty_chain_handle.clone(),
            chain_handle.clone(),
        );

        let result = submit_light_client_attack_evidence(
            &evidence,
            chain,
            counterparty_client,
            counterparty_client_id,
            counterparty_chain_handle,
            misbehaviour,
        );

        if let Err(error) = result {
            error!("{error}");
        }
    }

    Ok(())
}

fn submit_light_client_attack_evidence(
    evidence: &LightClientAttackEvidence,
    chain: &CosmosSdkChain,
    counterparty_client: ForeignClient<BaseChainHandle, BaseChainHandle>,
    counterparty_client_id: ClientId,
    counterparty: &BaseChainHandle,
    misbehaviour: TendermintMisbehaviour,
) -> Result<(), eyre::Error> {
    info!(
        "building misbehaviour evidence for client `{}` on chain `{}`",
        counterparty_client_id,
        counterparty.id(),
    );

    let signer = counterparty.get_signer()?;
    let common_height = Height::from_tm(evidence.common_height, chain.id());

    if counterparty_client.is_frozen() {
        warn!(
            "skipping client `{}` on chain `{}` as it is already frozen",
            counterparty_client_id,
            counterparty.id()
        );

        return Ok(());
    }

    let mut msgs = match counterparty_client.wait_and_build_update_client(common_height) {
        Ok(msgs) => msgs,

        Err(e) => {
            warn!(
                "skipping update client message for client `{}` on chain `{}`",
                counterparty_client_id,
                counterparty.id()
            );
            warn!("reason: failed to build update client message: {e}");

            vec![]
        }
    };

    if is_counterparty_provider(chain, counterparty) {
        info!(
            "will submit consumer light client attack evidence to client `{}` on provider chain `{}`",
            counterparty_client_id,
            counterparty.id(),
        );

        let msg = MsgSubmitIcsConsumerMisbehaviour {
            submitter: signer.clone(),
            misbehaviour: misbehaviour.clone(),
        }
        .to_any();

        msgs.push(msg);
    };

    info!(
        "will submit light client attack evidence to client `{}` on chain `{}`",
        counterparty_client_id,
        counterparty.id(),
    );

    let msg = MsgSubmitMisbehaviour {
        client_id: counterparty_client_id.clone(),
        misbehaviour: misbehaviour.to_any(),
        signer,
    }
    .to_any();

    msgs.push(msg);

    info!(
        "submitting light client attack evidence to client `{}` to chain `{}`",
        counterparty_client_id,
        counterparty.id(),
    );

    let tracked_msgs = TrackedMsgs::new_static(msgs, "light_client_attack_evidence");
    let responses = counterparty.send_messages_and_wait_check_tx(tracked_msgs)?;

    match responses.first() {
        Some(response) if response.code.is_ok() => {
            info!(
                "successfully submitted light client attack for client `{}` to chain `{}`, tx hash: {}",
                counterparty_client_id,
                counterparty.id(),
                response.hash
            );

            Ok(())
        }
        Some(response) => Err(eyre::eyre!(
            "failed to submit light client attack evidence to chain {}: {response:?}",
            counterparty.id()
        )),

        None => Err(eyre::eyre!(
            "failed to submit light client attack evidence to chain {}: no response from chain",
            counterparty.id()
        )),
    }
}

fn is_counterparty_provider(
    chain: &CosmosSdkChain,
    counterparty_chain_handle: &BaseChainHandle,
) -> bool {
    if chain.config().ccv_consumer_chain {
        let consumer_chains = counterparty_chain_handle
            .query_consumer_chains()
            .unwrap_or_default(); // If the query fails, use an empty list of consumers

        // FIXME: Do do we need to check if the client id also matches?
        // ie. is it okay to submit a `MsgSubmitIcsConsumerMisbehaviour` to all clients
        // of the provider chain, or should we only do this for the CCV client, and
        // use the standard message for other clients?
        consumer_chains
            .iter()
            .any(|(chain_id, _)| chain_id == chain.id())
    } else {
        false
    }
}

/// Fetch all the counterparty clients of the given chain.
/// A counterparty client is a client that has a connection with that chain.
///
/// 1. Fetch all connections on the given chain
/// 2. For each connection:
///     2.1. Fetch the client state of the counterparty client of that connection.
///     2.2. From the client state, extract the chain id of the counterparty chain.
/// 4. Return a list of all counterparty chains and counterparty clients.
fn fetch_all_counterparty_clients(
    chain: &CosmosSdkChain,
) -> eyre::Result<Vec<(ChainId, ClientId)>> {
    use ibc_relayer::chain::requests::{QueryClientStateRequest, QueryConnectionsRequest};

    let connections = chain.query_connections(QueryConnectionsRequest {
        pagination: Some(PageRequest::all()),
    })?;

    debug!("found {} connections", connections.len());

    let mut counterparty_clients = vec![];

    for connection in connections {
        debug!(
            "fetching counterparty client state for connection {}",
            connection.connection_id
        );

        let client_id = connection.connection_end.client_id();

        let client_state = chain.query_client_state(
            QueryClientStateRequest {
                client_id: client_id.clone(),
                height: QueryHeight::Latest,
            },
            IncludeProof::No,
        );

        let client_state = match client_state {
            Ok((client_state, _)) => client_state,
            Err(e) => {
                error!(
                    "failed to fetch client state for counterparty client {client_id}, skipping..."
                );
                error!("reason: {e}");

                continue;
            }
        };

        let counterparty_chain_id = client_state.chain_id();
        info!("found counterparty client with id {client_id} on counterparty chain {counterparty_chain_id}");

        if client_state.is_frozen() {
            info!("counterparty client {client_id} is already frozen, skipping...");
            continue;
        }

        counterparty_clients.push((counterparty_chain_id, client_id.clone()));
    }

    Ok(counterparty_clients)
}

/// Build the two headers to submit as part of the `MsgSubmitMisbehaviour` message.
fn build_evidence_headers(
    rt: Arc<TokioRuntime>,
    chain: &CosmosSdkChain,
    lc: LightClientAttackEvidence,
) -> eyre::Result<(TendermintHeader, TendermintHeader)> {
    let trusted_validator_set = rt
        .block_on(chain.rpc_client.validators(lc.common_height, Paging::All))?
        .validators;

    let header1 = {
        TendermintHeader {
            signed_header: lc.conflicting_block.signed_header,
            validator_set: lc.conflicting_block.validator_set,
            trusted_height: Height::from_tm(lc.common_height, chain.id()),
            trusted_validator_set: validator::Set::new(trusted_validator_set.clone(), None),
        }
    };

    let header2 = {
        let signed_header = rt
            .block_on(chain.rpc_client.commit(header1.signed_header.header.height))?
            .signed_header;

        let validators = rt
            .block_on(
                chain
                    .rpc_client
                    .validators(header1.signed_header.header.height, Paging::All),
            )?
            .validators;

        let validator_set =
            validator::Set::with_proposer(validators, signed_header.header.proposer_address)?;

        TendermintHeader {
            signed_header,
            validator_set,
            trusted_height: Height::from_tm(lc.common_height, chain.id()),
            trusted_validator_set: validator::Set::new(trusted_validator_set, None),
        }
    };

    Ok((header1, header2))
}

#[cfg(test)]
mod tests {
    use super::EvidenceCmd;

    use abscissa_core::clap::Parser;
    use ibc_relayer_types::core::ics24_host::identifier::ChainId;

    #[test]
    fn test_misbehaviour() {
        assert_eq!(
            EvidenceCmd {
                chain_id: ChainId::from_string("chain_id"),
                check_past_blocks: 100,
                key_name: None,
            },
            EvidenceCmd::parse_from(["test", "--chain", "chain_id"])
        )
    }

    #[test]
    fn test_misbehaviour_no_chain() {
        assert!(EvidenceCmd::try_parse_from(["test"]).is_err())
    }
}
