use std::convert::TryInto;
use std::str::FromStr;
use std::thread;
use std::time::Duration;

use abscissa_core::{config, error::BoxError, Command, Options, Runnable};
use prost_types::Any;

use ibc::downcast;
use ibc::events::{IBCEvent, IBCEventType};
use ibc::ics02_client::client_header::TENDERMINT_HEADER_TYPE_URL;
use ibc::ics02_client::client_state::AnyClientState;
use ibc::ics02_client::client_type::ClientType;
use ibc::ics02_client::height::Height;
use ibc::ics07_tendermint::header::QueryHeaderRequest;
use ibc::ics24_host::identifier::ChainId;
use ibc::query::QueryTxRequest;
use ibc_relayer::config::StoreConfig;
use ibc_relayer::foreign_client::ForeignClient;

use crate::application::CliApp;
use crate::commands::cli_utils::{spawn_chain_runtime, SpawnOptions};
use crate::conclude::Output;
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct MisbehaviourCmd {
    #[options(
        free,
        required,
        help = "identifier of the chain where client updates are monitored for misbehaviour"
    )]
    chain_id: ChainId,
}

impl Runnable for MisbehaviourCmd {
    fn run(&self) {
        let config = app_config();

        let res = monitor_misbehaviour(&self.chain_id, &config);
        match res {
            Ok(()) => Output::success(()).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

pub fn monitor_misbehaviour(
    chain_id: &ChainId,
    config: &config::Reader<CliApp>,
) -> Result<(), BoxError> {
    let spawn_options = SpawnOptions::override_store_config(StoreConfig::memory());

    let chain = spawn_chain_runtime(&spawn_options, &config, chain_id).unwrap();

    let subscription = chain.subscribe()?;

    while let Ok(event_batch) = subscription.recv() {
        for event in event_batch.events.iter() {
            match event {
                IBCEvent::UpdateClient(update) => {
                    dbg!(update);
                    // TODO - once event is updated in SDK we will do something like:
                    // let header = update.header_bytes();
                    // until then query Tx to get the header:
                    // --- start hack (remove up to end hack) ----
                    let request = QueryHeaderRequest {
                        event_id: IBCEventType::UpdateClient,
                        client_id: update.client_id().clone(),
                        consensus_height: *update.consensus_height(),
                        height: *update.height(),
                    };
                    // Tx query fails if we don't wait a bit here (block is not ready/ indexed?)
                    thread::sleep(Duration::from_millis(100));

                    let res = chain.query_txs(QueryTxRequest::Header(request)).unwrap();
                    assert_eq!(res.len(), 1);
                    let event = res[0].clone();
                    if let IBCEvent::UpdateClient2(update) = event {
                        // we assume here that the update event will include just the header bytes
                        // --- end hack ---

                        // 1 - make sure client is supported and create the counterparty chain handle
                        let client_id = update.client_id();
                        let client_state =
                            chain.query_client_state(client_id, Height::zero()).unwrap();
                        let tm_client_state =
                            downcast!(client_state => AnyClientState::Tendermint).unwrap();
                        let counterparty_chain = spawn_chain_runtime(
                            &spawn_options,
                            &config,
                            &ChainId::from_str(tm_client_state.chain_id.as_str()).unwrap(),
                        )
                        .unwrap();

                        // 2 - restore the foreign client
                        let client = ForeignClient::restore_client(
                            chain.clone(),
                            counterparty_chain.clone(),
                            client_id,
                        );

                        // 3 - decode light block from the update event
                        // TODO - code below may change depending on the header representation in the new update event
                        if update.client_type == ClientType::Tendermint {
                            let chain_header = Any {
                                type_url: TENDERMINT_HEADER_TYPE_URL.to_string(),
                                value: update.header_bytes().clone(),
                            };

                            let res = client
                                .handle_misbehaviour(
                                    update.consensus_height(),
                                    chain_header.try_into().unwrap(),
                                )
                                .unwrap();
                            println!("Handled misbehavior {:?}", res);
                        }
                    }
                }
                IBCEvent::CreateClient(create) => {
                    // TODO - get header from full node, consensus state from chain, compare
                }
                _ => {}
            }
        }
    }

    Ok(())
}
