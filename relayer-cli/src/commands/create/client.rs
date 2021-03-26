use abscissa_core::{Command, Options, Runnable};

use ibc::events::IbcEvent;
use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc_relayer::config::StoreConfig;
use ibc_relayer::foreign_client::ForeignClient;

use crate::commands::cli_utils::{ChainHandlePair, SpawnOptions};
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::error::{Error, Kind};
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct CreateClientCommand {
    #[options(
    free,
    required,
    help = "identifier of chain which will host this client"
    )]
    host_chain_id: ChainId,

    #[options(free, help = "identifier of the chain which this client will target, i.e., verify headers")]
    target_chain_id: ChainId,
}

// cargo run --bin hermes -- create client ibc-0 ibc-1
impl Runnable for CreateClientCommand {
    fn run(&self) {
        let config = app_config();

        let spawn_options = SpawnOptions::override_store_config(StoreConfig::memory());

        let chains =
            ChainHandlePair::spawn_with(spawn_options, &config, &self.target_chain_id, &self.host_chain_id)
                .unwrap_or_else(exit_with_unrecoverable_error);

        let client = ForeignClient {
            dst_chain: chains.dst,
            src_chain: chains.src,
            id: ClientId::default(),
        };

        // Trigger client creation via the "build" interface, so that we obtain the resulting event
        let res: Result<IbcEvent, Error> = client
            .build_create_client_and_send()
            .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}