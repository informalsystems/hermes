use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use core::str::FromStr;
use ibc::applications::ics29_fee::msgs::register_payee::build_register_payee_message;
use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::signer::Signer;
use ibc_relayer::chain::cosmos::encode::key_entry_to_signer;
use ibc_relayer::chain::cosmos::tx::simple_send_tx;
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::keyring::KeyRing;
use tokio::runtime::Runtime;

use crate::application::app_config;
use crate::error::Error;

#[derive(Clone, Command, Debug, Parser, PartialEq)]
#[clap(
    override_usage = "hermes keys add [OPTIONS] --chain <CHAIN_ID> --key-file <KEY_FILE>

    hermes keys add [OPTIONS] --chain <CHAIN_ID> --mnemonic-file <MNEMONIC_FILE>"
)]
pub struct RegisterPayeeCmd {
    #[clap(
        long = "chain",
        required = true,
        help_heading = "FLAGS",
        help = "Identifier of the chain"
    )]
    chain_id: ChainId,

    #[clap(
        long = "channel-id",
        required = true,
        help_heading = "FLAGS",
        help = "Channel ID"
    )]
    channel_id: ChannelId,

    #[clap(
        long = "port",
        required = true,
        help_heading = "FLAGS",
        help = "Port ID"
    )]
    port_id: PortId,

    #[clap(
        long = "payee-address",
        required = true,
        help_heading = "FLAGS",
        help = "Payee address"
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
        .unwrap()
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

    let chain_config = config
        .find_chain(chain_id)
        .ok_or_else(|| Error::missing_chain_config(chain_id.clone()))?;

    let tx_config = TxConfig::try_from(chain_config).map_err(Error::relayer)?;

    let keyring = KeyRing::new(
        chain_config.key_store_type,
        &chain_config.account_prefix,
        &chain_config.id,
    )
    .map_err(Error::key_ring)?;

    let key_entry = keyring
        .get_key(&chain_config.key_name)
        .map_err(Error::key_ring)?;

    let signer =
        key_entry_to_signer(&key_entry, &&chain_config.account_prefix).map_err(Error::relayer)?;

    let message =
        build_register_payee_message(&signer, &payee, &channel_id, &port_id).map_err(Error::fee)?;

    let runtime = Runtime::new().map_err(Error::io)?;

    runtime
        .block_on(simple_send_tx(&tx_config, &key_entry, vec![message]))
        .map_err(Error::relayer)?;

    Ok(())
}
