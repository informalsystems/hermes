//! `update` subcommand

use abscissa_core::{Command, Help, Options, Runnable};
use ibc::events::IbcEvent;
use ibc::ics02_client::client_state::ClientState;
use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc::NonZeroHeight;
use ibc_relayer::foreign_client::ForeignClient;

use crate::application::app_config;
use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::Output;

#[derive(Clone, Command, Debug, Options)]
pub struct UpdateClientCmd {
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
}

impl UpdateClientCmd {
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

        let trusted_height = client
            .latest_consensus_state_height()
            .map_err(|e| e.to_string())?;

        client
            .build_update_client_and_send(target_height, trusted_height)
            .map_err(|e| e.to_string())
    }
}

impl Runnable for UpdateClientCmd {
    fn run(&self) {
        match self.execute() {
            Ok(receipt) => Output::success(receipt).exit(),
            Err(e) => Output::error(e).exit(),
        }
    }
}

#[derive(Command, Debug, Options, Runnable)]
pub enum UpdateCmds {
    /// Generic `help`
    #[options(help = "Get usage information")]
    Help(Help<Self>),

    /// Subcommand for updating a `client`
    #[options(help = "Update an IBC client")]
    Client(UpdateClientCmd),
}
