use abscissa_core::{config, Command, Options, Runnable};

use ibc::events::IbcEvent;
use ibc::ics02_client::client_state::ClientState;
use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc_proto::ibc::core::client::v1::QueryClientStatesRequest;
use ibc_relayer::foreign_client::ForeignClient;

use crate::application::{app_config, CliApp};
use crate::cli_utils::{spawn_chain_runtime, ChainHandlePair};
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::error::{Error, Kind};

#[derive(Clone, Command, Debug, Options)]
pub struct TxCreateClientCmd {
    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,
}

/// Sample to run this tx:
///     `hermes tx raw create-client ibc-0 ibc-1`
impl Runnable for TxCreateClientCmd {
    fn run(&self) {
        let config = app_config();

        if self.src_chain_id == self.dst_chain_id {
            Output::error("source and destination chains must be different".to_string()).exit()
        }

        let chains = match ChainHandlePair::spawn(&config, &self.src_chain_id, &self.dst_chain_id) {
            Ok(chains) => chains,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        let client = ForeignClient::restore(ClientId::default(), chains.dst, chains.src);

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

#[derive(Clone, Command, Debug, Options)]
pub struct TxUpdateClientCmd {
    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[options(
        free,
        required,
        help = "identifier of the client to be updated on destination chain"
    )]
    dst_client_id: ClientId,

    #[options(help = "the target height of the client update", short = "h")]
    target_height: Option<u64>,

    #[options(help = "the trusted height of the client update", short = "t")]
    trusted_height: Option<u64>,
}

impl Runnable for TxUpdateClientCmd {
    fn run(&self) {
        let config = app_config();

        let dst_chain = match spawn_chain_runtime(&config, &self.dst_chain_id) {
            Ok(handle) => handle,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        let src_chain_id =
            match dst_chain.query_client_state(&self.dst_client_id, ibc::Height::zero()) {
                Ok(cs) => cs.chain_id(),
                Err(e) => {
                    return Output::error(format!(
                        "Query of client '{}' on chain '{}' failed with error: {}",
                        self.dst_client_id, self.dst_chain_id, e
                    ))
                    .exit()
                }
            };

        let src_chain = match spawn_chain_runtime(&config, &src_chain_id) {
            Ok(handle) => handle,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        let height = match self.target_height {
            Some(height) => ibc::Height::new(src_chain.id().version(), height),
            None => ibc::Height::zero(),
        };

        let trusted_height = match self.trusted_height {
            Some(height) => ibc::Height::new(src_chain.id().version(), height),
            None => ibc::Height::zero(),
        };

        let client = ForeignClient::find(src_chain, dst_chain, &self.dst_client_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let res = client
            .build_update_client_and_send(height, trusted_height)
            .map_err(|e| Kind::Tx.context(e));

        match res {
            Ok(events) => Output::success(events).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxUpgradeClientCmd {
    #[options(free, required, help = "identifier of the chain that hosts the client")]
    chain_id: ChainId,

    #[options(free, required, help = "identifier of the client to be upgraded")]
    client_id: ClientId,
}

impl Runnable for TxUpgradeClientCmd {
    fn run(&self) {
        let config = app_config();

        let dst_chain = match spawn_chain_runtime(&config, &self.chain_id) {
            Ok(handle) => handle,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        let src_chain_id = match dst_chain.query_client_state(&self.client_id, ibc::Height::zero())
        {
            Ok(cs) => cs.chain_id(),
            Err(e) => {
                return Output::error(format!(
                    "Query of client '{}' on chain '{}' failed with error: {}",
                    self.client_id, self.chain_id, e
                ))
                .exit()
            }
        };

        let src_chain = match spawn_chain_runtime(&config, &src_chain_id) {
            Ok(handle) => handle,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        let client = ForeignClient::find(src_chain, dst_chain, &self.client_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        let outcome = client.upgrade();

        match outcome {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxUpgradeClientsCmd {
    #[options(free, required, help = "identifier of the chain that must be upgraded")]
    src_chain_id: ChainId,
}

impl Runnable for TxUpgradeClientsCmd {
    fn run(&self) {
        let config = app_config();

        let outputs: Vec<Output> = config
            .chains
            .iter()
            .map(|chain| match self.upgrade_chain(&config, &chain.id) {
                Ok(receipts) => Output::success(receipts),
                Err(e) => Output::error(e),
            })
            .collect();

        Output::combined(outputs.into_iter()).exit()
    }
}

impl TxUpgradeClientsCmd {
    fn upgrade_chain(
        &self,
        config: &config::Reader<CliApp>,
        dst_chain_id: &ChainId,
    ) -> Result<Vec<IbcEvent>, Error> {
        let chains = ChainHandlePair::spawn(&config, &self.src_chain_id, dst_chain_id)?;

        let req = QueryClientStatesRequest {
            pagination: ibc_proto::cosmos::base::query::pagination::all(),
        };
        let client_ids: Vec<ClientId> = chains
            .dst
            .query_clients(req)
            .map_err(|e| Kind::Query.context(e))?
            .iter()
            .filter_map(|cs| {
                if self.src_chain_id == cs.client_state.chain_id() {
                    Some(cs.client_id.clone())
                } else {
                    None
                }
            })
            .collect();

        debug_assert!(client_ids.len() < 2);

        let mut events = vec![];
        if let Some(client_id) = client_ids.first() {
            let client = ForeignClient::find(chains.src.clone(), chains.dst.clone(), client_id)
                .map_err(|e| Kind::Query.context(e))?;
            events = client.upgrade().map_err(|e| Kind::Query.context(e))?
        }

        Ok(events)
    }
}
