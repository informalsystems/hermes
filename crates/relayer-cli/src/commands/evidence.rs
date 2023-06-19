use alloc::sync::Arc;
use std::cmp::min;
use std::ops::Deref;
use tokio::runtime::Runtime as TokioRuntime;

use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use ibc_relayer::chain::endpoint::ChainEndpoint;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use ibc_relayer_types::events::IbcEvent;

use crate::conclude::Output;
use crate::prelude::*;
use ibc_relayer::chain::cosmos::CosmosSdkChain;
use ibc_relayer_types::core::ics02_client::height::Height;

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

        let mut chain = CosmosSdkChain::bootstrap(chain_config, rt.clone()).unwrap();

        // let res =
        //     if !chain_config.ccv_consumer_chain {
        //         monitor_equivocation(&mut chain)
        //     } else {
        //         Ok(None)
        //     };

        let res = rt.block_on(monitor_equivocation(&mut chain));

        match res {
            Ok(some_event) => Output::success(some_event).exit(),
            Err(e) => Output::error(e).exit(),
        }
    }
}

async fn monitor_equivocation(chain: &mut CosmosSdkChain) -> eyre::Result<Option<IbcEvent>> {
    let subscription = chain.subscribe()?;

    // check previous blocks for equivocation that may have been missed
    let tm_latest_height = chain
        .rpc_client
        .status()
        .await?
        .sync_info
        .latest_block_height;

    let latest_height = Height::new(chain.id().version(), tm_latest_height.value()).unwrap();
    let num_blocks = min(tm_latest_height.value(), 100);
    let mut height = latest_height;

    for _h in 0..num_blocks - 1 {
        debug!("trying to check for evidence at height {height}");

        equivocation_handling(chain, height).await?;

        height = height.decrement().unwrap();
    }

    // process new block events
    while let Ok(event_batch) = subscription.recv() {
        match event_batch.deref() {
            Ok(event_batch) => {
                for event_with_height in &event_batch.events {
                    if let IbcEvent::NewBlock(new_block) = &event_with_height.event {
                        debug!("{new_block:?}");

                        equivocation_handling(chain, new_block.height).await?;
                    }
                }
            }
            Err(e) => {
                dbg!(e);
            }
        }
    }

    Ok(None)
}

use tendermint_rpc::Client;

async fn equivocation_handling(chain: &CosmosSdkChain, height: Height) -> eyre::Result<()> {
    let tm_height = tendermint::block::Height::try_from(height.revision_height()).unwrap();
    let evidence_list = chain.rpc_client.block(tm_height).await?.block.evidence;
    for evidence in evidence_list.iter() {
        match evidence {
            tendermint::evidence::Evidence::DuplicateVote(dv) => {
                debug!("found duplicate vote evidence {dv:?}");
            }
            tendermint::evidence::Evidence::LightClientAttack(lc) => {
                debug!("found light client attack evidence {lc:?}");
            }
        }
    }

    Ok(())
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
