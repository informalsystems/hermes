use alloc::sync::Arc;
use ibc_relayer::chain::tracking::TrackedMsgs;
use ibc_relayer_types::core::ics02_client::msgs::misbehaviour::MsgSubmitMisbehaviour;
use ibc_relayer_types::tx_msg::Msg;
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
use ibc_relayer_types::clients::ics07_tendermint::header::Header as TendermintHeader;
use ibc_relayer_types::clients::ics07_tendermint::misbehaviour::Misbehaviour as TendermintMisbehaviour;
use ibc_relayer_types::core::ics02_client::height::Height;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId};
use ibc_relayer_types::events::IbcEvent;

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

        let chain = CosmosSdkChain::bootstrap(chain_config, rt.clone()).unwrap();
        let res = rt.block_on(monitor_equivocation(rt.clone(), chain));

        match res {
            Ok(()) => Output::success(()).exit(),
            Err(e) => Output::error(e).exit(),
        }
    }
}

async fn monitor_equivocation(
    rt: Arc<TokioRuntime>,
    mut chain: CosmosSdkChain,
) -> eyre::Result<()> {
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

                        check_misbehaviour_at(rt.clone(), &chain, new_block.height).await?;
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

#[allow(unused_variables, unreachable_code, clippy::diverging_sub_expression)]
async fn check_misbehaviour_at(
    rt: Arc<TokioRuntime>,
    chain: &CosmosSdkChain,
    height: Height,
) -> eyre::Result<()> {
    let block = chain
        .rpc_client
        .block(TendermintHeight::from(height))
        .await?
        .block;

    for evidence in block.evidence.into_vec() {
        match evidence {
            tendermint::evidence::Evidence::DuplicateVote(dv) => {
                debug!("found duplicate vote evidence {dv:?}");
            }
            tendermint::evidence::Evidence::LightClientAttack(lc) => {
                debug!("found light client attack evidence {lc:?}");

                handle_light_client_attack(rt.clone(), chain, *lc).await?;
            }
        }
    }

    Ok(())
}

async fn handle_light_client_attack(
    rt: Arc<TokioRuntime>,
    chain: &CosmosSdkChain,
    lc: LightClientAttackEvidence,
) -> eyre::Result<()> {
    let trusted_validator_set = chain
        .rpc_client
        .validators(lc.common_height, Paging::All)
        .await?
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
        let signed_header = chain
            .rpc_client
            .commit(header1.signed_header.header.height)
            .await?
            .signed_header;

        let validators = chain
            .rpc_client
            .validators(header1.signed_header.header.height, Paging::All)
            .await?
            .validators;

        TendermintHeader {
            signed_header,
            validator_set: validator::Set::new(validators, None),
            trusted_height: Height::from_tm(lc.common_height, chain.id()),
            trusted_validator_set: validator::Set::new(trusted_validator_set, None),
        }
    };

    let counterparty_clients = fetch_all_counterparty_clients(chain).await?;

    for (counterparty_chain_id, counterparty_client_id) in counterparty_clients {
        let misbehavior = TendermintMisbehaviour {
            client_id: counterparty_client_id.clone(),
            header1: header1.clone(),
            header2: header2.clone(),
        };

        // TODO: Cache chain handles
        let mut counterparty_chain = {
            let config = app_config();
            let chain_config = config
                .find_chain(&counterparty_chain_id)
                .cloned()
                .ok_or_else(|| {
                    eyre::eyre!("cannot find chain config for chain {counterparty_chain_id}")
                })?;

            CosmosSdkChain::bootstrap(chain_config, rt.clone())?
        };

        let msg = MsgSubmitMisbehaviour {
            client_id: counterparty_client_id,
            misbehaviour: misbehavior.to_any(),
            signer: counterparty_chain.get_signer()?,
        };

        let tracked_msgs = TrackedMsgs::new_single(msg.to_any(), "submit_misbehaviour");
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

async fn fetch_all_counterparty_clients(
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
