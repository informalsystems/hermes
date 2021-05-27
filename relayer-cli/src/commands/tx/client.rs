use abscissa_core::{Command, Options, Runnable};

use ibc::events::IbcEvent;
use ibc::ics02_client::client_state::ClientState;
use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc::NonZeroHeight;
use ibc_relayer::foreign_client::ForeignClient;

use crate::application::app_config;
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

impl TxUpdateClientCmd {
    fn execute(&self) -> Result<Option<IbcEvent>, String> {
        let config = app_config();

        let dst_chain =
            spawn_chain_runtime(&config, &self.dst_chain_id).map_err(|e| format!("{}", e))?;

        let src_chain_id = dst_chain
            .query_client_state(&self.dst_client_id, ibc::Height::zero())
            .map_err(|e| {
                format!(
                    "Query of client '{}' on chain '{}' failed with error: {}",
                    self.dst_client_id, self.dst_chain_id, e
                )
            })?
            .chain_id();

        let src_chain =
            spawn_chain_runtime(&config, &src_chain_id).map_err(|e| format!("{}", e))?;

        let src_chain_id = src_chain.id().version();

        let client = ForeignClient::find(src_chain, dst_chain, &self.dst_client_id)
            .map_err(|e| format!("failed to find foreign client: {}", e))?;

        let m_target_height = self
            .target_height
            .and_then(|h| NonZeroHeight::new(ibc::Height::new(src_chain_id, h)));

        let m_trusted_height = self.trusted_height.map(|h| {
            // Allow trusted height parameter to be zero if force provided
            NonZeroHeight::unsafe_new(ibc::Height::new(src_chain_id, h))
        });

        let target_height = match m_target_height {
            Some(height) => {
                client.wait_src_chain_reach_height(height).map_err(|e| {
                    format!(
                        "failed to wait for client to reach height {}: {}",
                        height, e
                    )
                })?;
                height
            }
            None => client
                .latest_src_chain_height()
                .map_err(|e| e.to_string())?,
        };

        let trusted_height = match m_trusted_height {
            Some(h) => h,
            None => client
                .latest_consensus_state_height()
                .map_err(|e| e.to_string())?,
        };

        client
            .build_update_client_and_send(target_height, trusted_height)
            .map_err(|e| e.to_string())
    }
}

impl Runnable for TxUpdateClientCmd {
    fn run(&self) {
        match self.execute() {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(e).exit(),
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
