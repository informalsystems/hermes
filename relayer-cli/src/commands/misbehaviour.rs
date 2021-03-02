use std::convert::TryFrom;
use std::str::FromStr;

use abscissa_core::{Command, config, error::BoxError, Options, Runnable};
use prost_types::Any;

use ibc::downcast;
use ibc::events::IbcEvent;
use ibc::ics02_client::client_header::AnyHeader;
use ibc::ics02_client::client_state::AnyClientState;
use ibc::ics02_client::height::Height;
use ibc::ics24_host::identifier::ChainId;
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
                IbcEvent::UpdateClient(update) => {
                    dbg!(update);
                    // 1 - make sure client is supported and then create the counterparty chain handle
                    let client_id = update.client_id();
                    let client_state = chain.query_client_state(client_id, Height::zero()).unwrap();
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
                    let valid_raw_bytes=  update.header.as_bytes();

                    let any: Any = prost::Message::decode(valid_raw_bytes).unwrap();
                    let header: AnyHeader = AnyHeader::try_from(any).unwrap();
                    let res = client
                        .handle_misbehaviour(
                            update.consensus_height(),
                            header,
                        )
                        .unwrap();
                    println!("Handled misbehavior {:?}", res);
                }

                IbcEvent::CreateClient(create) => {
                    // TODO - get header from full node, consensus state from chain, compare
                }
                _ => {}
            }
        }
    }

    Ok(())
}
