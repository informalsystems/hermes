use alloc::sync::Arc;
use std::collections::HashMap;
use std::ops::Deref;

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use tokio::runtime::Runtime as TokioRuntime;

use tendermint::block::Height as TendermintHeight;
use tendermint::evidence::LightClientAttackEvidence;
use tendermint::validator;

use ibc_relayer::chain::cosmos::CosmosSdkChain;
use ibc_relayer::chain::endpoint::ChainEndpoint;
use ibc_relayer::chain::requests::{IncludeProof, QueryHeight};
use ibc_relayer::chain::tracking::TrackedMsgs;
use ibc_relayer::chain::ChainType;
use ibc_relayer_types::applications::ics28_ccv::msgs::ccv_misbehaviour::MsgSubmitIcsConsumerMisbehaviour;
use ibc_relayer_types::clients::ics07_tendermint::header::Header as TendermintHeader;
use ibc_relayer_types::clients::ics07_tendermint::misbehaviour::Misbehaviour as TendermintMisbehaviour;
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
}

impl Runnable for EvidenceCmd {
    fn run(&self) {
        let config = app_config();
        let rt = Arc::new(TokioRuntime::new().unwrap());
        let chain_config = config.find_chain(&self.chain_id).cloned().unwrap();

        if chain_config.r#type != ChainType::CosmosSdk {
            Output::error(format!("Chain {} is not a Cosmos SDK chain", self.chain_id)).exit();
        }

        let chain = CosmosSdkChain::bootstrap(chain_config, rt.clone()).unwrap();
        let res = monitor_misbehaviours(rt, chain);

        match res {
            Ok(()) => Output::success(()).exit(),
            Err(e) => Output::error(e).exit(),
        }
    }
}

fn monitor_misbehaviours(rt: Arc<TokioRuntime>, mut chain: CosmosSdkChain) -> eyre::Result<()> {
    let subscription = chain.subscribe()?;

    // check previous blocks for equivocation that may have been missed
    // let tm_latest_height = chain
    //     .rpc_client
    //     .status()
    //     .await?
    //     .sync_info
    //     .latest_block_height;
    //
    // let latest_height = Height::new(chain.id().version(), tm_latest_height.value()).unwrap();
    // let num_blocks = min(tm_latest_height.value(), 100);
    // let mut height = latest_height;
    //
    // for _height in 0..num_blocks - 1 {
    //     debug!("trying to check for evidence at height {height}");
    //
    //     equivocation_handling(&chain, height).await?;
    //
    //     height = height.decrement().unwrap();
    // }

    // process new block events
    while let Ok(event_batch) = subscription.recv() {
        match event_batch.deref() {
            Ok(event_batch) => {
                for event_with_height in &event_batch.events {
                    if let IbcEvent::NewBlock(new_block) = &event_with_height.event {
                        debug!("{new_block:?}");

                        check_misbehaviour_at(rt.clone(), &chain, new_block.height)?;
                    }
                }
            }
            Err(e) => {
                dbg!(e);
            }
        }
    }

    Ok(())
}

use tendermint_rpc::{Client, Paging};

/// Check for misbehaviour evidence in the block at the given height.
/// If such evidence is found, handle it by submitting it to all counterparty
/// clients of the chain, freezing them.
fn check_misbehaviour_at(
    rt: Arc<TokioRuntime>,
    chain: &CosmosSdkChain,
    height: Height,
) -> eyre::Result<()> {
    let block = rt
        .block_on(chain.rpc_client.block(TendermintHeight::from(height)))?
        .block;

    for evidence in block.evidence.into_vec() {
        match evidence {
            tendermint::evidence::Evidence::DuplicateVote(dv) => {
                debug!("found duplicate vote evidence {dv:?}");
            }
            tendermint::evidence::Evidence::LightClientAttack(lc) => {
                debug!("found light client attack evidence {lc:?}");

                handle_light_client_attack(rt.clone(), chain, *lc)?;
            }
        }
    }

    Ok(())
}

fn handle_light_client_attack(
    rt: Arc<TokioRuntime>,
    chain: &CosmosSdkChain,
    lc: LightClientAttackEvidence,
) -> eyre::Result<()> {
    // Build the two headers to submit as part of the `MsgSubmitMisbehaviour` message.
    let (header1, header2) = build_evidence_headers(rt.clone(), chain, lc)?;

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

        if !chains.contains_key(&counterparty_chain_id) {
            let chain = spawn_chain_by_id(rt.clone(), &counterparty_chain_id)?;
            chains.insert(counterparty_chain_id.clone(), chain);
        };

        let counterparty_chain = chains
            .get_mut(&counterparty_chain_id)
            .ok_or_else(|| eyre::eyre!("failed to spawn chain {counterparty_chain_id}"))?;

        let signer = counterparty_chain.get_signer()?;

        // If the misbehaving chain is a CCV consumer chain,
        // then try fetch the consumer chains of the counterparty chains.
        // If that fails, then that chain is not a provider chain.
        // Otherwise, check if the misbehaving chain is a consumer of the counterparty chain,
        // which is definitely a provider.
        let counterparty_is_provider = if chain.config().ccv_consumer_chain {
            let consumer_chains = counterparty_chain
                .query_consumer_chains()
                .unwrap_or_default(); // If the query fails, use an empty list of consumers

            consumer_chains
                .iter()
                .any(|(chain_id, _)| chain_id == chain.id())
        } else {
            false
        };

        let msg = if counterparty_is_provider {
            info!("submitting CCV misbehaviour to provider chain {counterparty_chain_id}");

            MsgSubmitIcsConsumerMisbehaviour {
                submitter: signer,
                misbehaviour,
            }
            .to_any()
        } else {
            info!("submitting sovereign misbehaviour to chain {counterparty_chain_id}");

            MsgSubmitMisbehaviour {
                client_id: counterparty_client_id,
                misbehaviour: misbehaviour.to_any(),
                signer,
            }
            .to_any()
        };

        let tracked_msgs = TrackedMsgs::new_single(msg, "submit_misbehaviour");
        let responses = counterparty_chain.send_messages_and_wait_check_tx(tracked_msgs)?;

        for response in responses {
            if response.code.is_ok() {
                info!("successfully submitted misbehaviour to chain {counterparty_chain_id}, tx hash: {}", response.hash);
            } else {
                error!(
                    "failed to submit misbehaviour to chain {counterparty_chain_id}: {response:?}"
                );
            }
        }
    }

    Ok(())
}

fn spawn_chain_by_id(
    rt: Arc<TokioRuntime>,
    counterparty_chain_id: &ChainId,
) -> Result<CosmosSdkChain, eyre::ErrReport> {
    let config = app_config();

    let chain_config = config
        .find_chain(counterparty_chain_id)
        .cloned()
        .ok_or_else(|| eyre::eyre!("cannot find chain config for chain {counterparty_chain_id}"))?;

    if chain_config.r#type != ChainType::CosmosSdk {
        return Err(eyre::eyre!(
            "chain {counterparty_chain_id} is not a Cosmos SDK chain"
        ));
    }

    let chain = CosmosSdkChain::bootstrap(chain_config, rt)?;

    Ok(chain)
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
    use ibc_relayer::chain::requests::PageRequest;
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

        let (client_state, _) = chain.query_client_state(
            QueryClientStateRequest {
                client_id: client_id.clone(),
                height: QueryHeight::Latest,
            },
            IncludeProof::No,
        )?;

        let counterparty_chain_id = client_state.chain_id();

        debug!(
            "found counterparty client with id {client_id} on counterparty chain {counterparty_chain_id}"
        );

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

        TendermintHeader {
            signed_header,
            validator_set: validator::Set::new(validators, None),
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
            },
            EvidenceCmd::parse_from(["test", "--chain", "chain_id"])
        )
    }

    #[test]
    fn test_misbehaviour_no_chain() {
        assert!(EvidenceCmd::try_parse_from(["test"]).is_err())
    }
}
