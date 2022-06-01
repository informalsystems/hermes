use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::requests::QueryChannelClientStateRequest;

use crate::application::app_config;
use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::{exit_with_unrecoverable_error, Output};

/// The data structure that represents the arguments when invoking the `query channel client` CLI command.
///
/// `query channel client --port-id <port_id> --channel-id <channel_id> <chain_id>`
///
/// If successful the channel's client state is displayed.
#[derive(Clone, Command, Debug, Parser)]
pub struct QueryChannelClientCmd {
    #[clap(required = true, help = "identifier of the chain to query")]
    chain_id: ChainId,

    #[clap(required = true, long, help = "identifier of the port to query")]
    port_id: PortId,

    #[clap(required = true, long, help = "identifier of the channel to query")]
    channel_id: ChannelId,
}

impl Runnable for QueryChannelClientCmd {
    fn run(&self) {
        let config = app_config();

        let chain = spawn_chain_runtime(&config, &self.chain_id)
            .unwrap_or_else(exit_with_unrecoverable_error);

        match chain.query_channel_client_state(QueryChannelClientStateRequest {
            port_id: self.port_id.clone(),
            channel_id: self.channel_id,
        }) {
            Ok(cs) => Output::success(cs).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
