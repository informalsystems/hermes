use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use core::str::FromStr;
use ibc::applications::ics29_fee::msgs::register_payee::build_register_payee_message;
use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::signer::Signer;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::tracking::TrackedMsgs;

use crate::application::app_config;
use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::error::Error;

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct RegisterPayeeCmd {
    #[clap(
        long = "chain",
        required = true,
        help_heading = "FLAGS",
        help = "Identifier of the chain"
    )]
    chain_id: ChainId,

    #[clap(
        long = "channel",
        required = true,
        help_heading = "FLAGS",
        help = "Identifier of the channel"
    )]
    channel_id: ChannelId,

    #[clap(
        long = "port",
        required = true,
        help_heading = "FLAGS",
        help = "Identifier of the port"
    )]
    port_id: PortId,

    #[clap(
        long = "payee",
        required = true,
        help_heading = "FLAGS",
        help = "Address of the payee"
    )]
    payee_address: String,
}

impl Runnable for RegisterPayeeCmd {
    fn run(&self) {
        run_register_payee_command(
            &self.chain_id,
            &self.channel_id,
            &self.port_id,
            &self.payee_address,
        )
        .unwrap_or_else(exit_with_unrecoverable_error);

        Output::success_msg("Successfully registered payee").exit()
    }
}

fn run_register_payee_command(
    chain_id: &ChainId,
    channel_id: &ChannelId,
    port_id: &PortId,
    payee_address: &str,
) -> Result<(), Error> {
    let payee = Signer::from_str(payee_address).map_err(Error::signer)?;

    let config = app_config();

    let chain_handle = spawn_chain_runtime(&config, chain_id)?;

    let signer = chain_handle.get_signer().map_err(Error::relayer)?;

    let message =
        build_register_payee_message(&signer, &payee, channel_id, port_id).map_err(Error::fee)?;

    let messages = TrackedMsgs::new_static(vec![message], "cli");

    chain_handle
        .send_messages_and_wait_commit(messages)
        .map_err(Error::relayer)?;

    Ok(())
}
