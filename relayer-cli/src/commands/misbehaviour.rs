use abscissa_core::{config, Command, Options, Runnable};
use ibc::events::IbcEvent;
use ibc::ics02_client::events::UpdateClient;
use ibc::ics02_client::height::Height;
use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::foreign_client::{ForeignClient, MisbehaviourResults};
use std::ops::Deref;

use crate::application::CliApp;
use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::Output;
use crate::prelude::*;
use ibc::ics02_client::client_state::ClientState;

#[derive(Clone, Command, Debug, Options)]
pub struct MisbehaviourCmd {
    #[options(
        free,
        required,
        help = "identifier of the chain where client updates are monitored for misbehaviour"
    )]
    chain_id: ChainId,

    #[options(
        free,
        required,
        help = "identifier of the client to be monitored for misbehaviour"
    )]
    client_id: ClientId,
}

impl Runnable for MisbehaviourCmd {
    fn run(&self) {
        let config = app_config();

        let res = monitor_misbehaviour(&self.chain_id, &self.client_id, &config);
        match res {
            Ok(some_event) => Output::success(some_event).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

pub fn monitor_misbehaviour(
    chain_id: &ChainId,
    client_id: &ClientId,
    config: &config::Reader<CliApp>,
) -> Result<Option<IbcEvent>, Box<dyn std::error::Error>> {
    let chain = spawn_chain_runtime(config, chain_id)
        .map_err(|e| format!("could not spawn the chain runtime for {}: {}", chain_id, e))?;

    let subscription = chain.subscribe()?;

    // check previous updates that may have been missed
    misbehaviour_handling(chain.clone(), config, client_id.clone(), None)?;

    // process update client events
    while let Ok(event_batch) = subscription.recv() {
        match event_batch.deref() {
            Ok(event_batch) => {
                for event in &event_batch.events {
                    match event {
                        IbcEvent::UpdateClient(update) => {
                            debug!("{:?}", update);
                            misbehaviour_handling(
                                chain.clone(),
                                config,
                                update.client_id().clone(),
                                Some(update.clone()),
                            )?;
                        }

                        IbcEvent::CreateClient(_create) => {
                            // TODO - get header from full node, consensus state from chain, compare
                        }

                        IbcEvent::ClientMisbehaviour(ref _misbehaviour) => {
                            // TODO - submit misbehaviour to the witnesses (our full node)
                            return Ok(Some(event.clone()));
                        }

                        _ => {}
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

fn misbehaviour_handling(
    chain: Box<dyn ChainHandle>,
    config: &config::Reader<CliApp>,
    client_id: ClientId,
    update: Option<UpdateClient>,
) -> Result<(), Box<dyn std::error::Error>> {
    let client_state = chain
        .query_client_state(&client_id, Height::zero())
        .map_err(|e| format!("could not query client state for {}: {}", client_id, e))?;

    if client_state.is_frozen() {
        return Err(format!("client {} is already frozen", client_id).into());
    }

    let counterparty_chain =
        spawn_chain_runtime(config, &client_state.chain_id()).map_err(|e| {
            format!(
                "could not spawn the chain runtime for {}: {}",
                client_state.chain_id(),
                e
            )
        })?;

    let client = ForeignClient::restore(client_id, chain, counterparty_chain);
    let result = client.detect_misbehaviour_and_submit_evidence(update);
    if let MisbehaviourResults::EvidenceSubmitted(events) = result {
        info!("evidence submission result {:?}", events);
    }

    Ok(())
}
