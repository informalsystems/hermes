use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use core::str::FromStr;
use ibc::applications::ics29_fee::msgs::register_payee::build_register_counterparty_payee_message;
use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::signer::Signer;
use ibc_relayer::chain::handle::ChainHandle;
use ibc_relayer::chain::tracking::TrackedMsgs;

use crate::application::app_config;
use crate::cli_utils::spawn_chain_runtime;
use crate::conclude::{exit_with_unrecoverable_error, Output};
use crate::error::Error;

#[derive(Clone, Command, Debug, Parser, PartialEq, Eq)]
pub struct RegisterCounterpartyPayeeCmd {
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
        long = "counterparty-payee",
        required = true,
        help_heading = "FLAGS",
        help = "Address of the counterparty payee"
    )]
    counterparty_payee_address: String,
}

impl Runnable for RegisterCounterpartyPayeeCmd {
    fn run(&self) {
        run_register_counterparty_payee_command(
            &self.chain_id,
            &self.channel_id,
            &self.port_id,
            &self.counterparty_payee_address,
        )
        .unwrap_or_else(exit_with_unrecoverable_error);

        Output::success_msg("Successfully registered counterparty payee").exit()
    }
}

fn run_register_counterparty_payee_command(
    chain_id: &ChainId,
    channel_id: &ChannelId,
    port_id: &PortId,
    counterparty_payee_address: &str,
) -> Result<(), Error> {
    let counterparty_payee = Signer::from_str(counterparty_payee_address).map_err(Error::signer)?;

    let config = app_config();

    let chain_handle = spawn_chain_runtime(&config, chain_id)?;

    let signer = chain_handle.get_signer().map_err(Error::relayer)?;

    let message = build_register_counterparty_payee_message(
        &signer,
        &counterparty_payee,
        channel_id,
        port_id,
    )
    .map_err(Error::fee)?;

    let messages = TrackedMsgs::new_static(vec![message], "cli");

    chain_handle
        .send_messages_and_wait_commit(messages)
        .map_err(Error::relayer)?;

    Ok(())
}
