use abscissa_core::{Command, Options, Runnable};

use ibc::events::IBCEvent;
use ibc::ics24_host::identifier::{ChainId, ClientId};
use relayer::config::StoreConfig;
use relayer::foreign_client::ForeignClient;

use crate::application::app_config;
use crate::commands::cli_utils::{ChainHandlePair, SpawnOptions};
use crate::conclude::Output;
use crate::error::{Error, Kind};

#[derive(Clone, Command, Debug, Options)]
pub struct TxCreateClientCmd {
    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,
}

/// Sample to run this tx:
///     `rrly -c loop_config.toml tx raw create-client ibc-0 ibc-1`
impl Runnable for TxCreateClientCmd {
    fn run(&self) {
        let config = app_config();

        let spawn_options = SpawnOptions::override_store_config(StoreConfig::memory());
        let chains = match ChainHandlePair::spawn_with(
            spawn_options,
            &config,
            &self.src_chain_id,
            &self.dst_chain_id,
        ) {
            Ok(chains) => chains,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        let client = ForeignClient {
            dst_chain: chains.dst,
            src_chain: chains.src,
            id: ClientId::default(),
        };

        // Trigger client creation via the "build" interface, so that we obtain the resulting event
        let res: Result<IBCEvent, Error> = client
            .build_create_client_and_send()
            .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxUpdateClientCmd {
    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[options(
        free,
        required,
        help = "identifier of the client to be updated on destination chain"
    )]
    dst_client_id: ClientId,
}

impl Runnable for TxUpdateClientCmd {
    fn run(&self) {
        let config = app_config();

        let spawn_options = SpawnOptions::override_store_config(StoreConfig::memory());
        let chains = match ChainHandlePair::spawn_with(
            spawn_options,
            &config,
            &self.src_chain_id,
            &self.dst_chain_id,
        ) {
            Ok(chains) => chains,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        let client = ForeignClient {
            dst_chain: chains.dst,
            src_chain: chains.src,
            id: self.dst_client_id.clone(),
        };

        let res: Result<IBCEvent, Error> = client
            .build_update_client_and_send()
            .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
