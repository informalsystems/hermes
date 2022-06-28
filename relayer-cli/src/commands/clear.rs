use abscissa_core::clap::Parser;
use abscissa_core::config::Override;
use abscissa_core::{Command, FrameworkErrorKind, Runnable};

use ibc::core::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc::events::IbcEvent;
use ibc_relayer::chain::handle::{BaseChainHandle, ChainHandle};
use ibc_relayer::config::Config;
use ibc_relayer::link::error::LinkError;
use ibc_relayer::link::{Link, LinkParameters};

use crate::application::app_config;
use crate::cli_utils::spawn_chain_counterparty;
use crate::conclude::Output;
use crate::error::Error;

/// `clear` subcommands
#[derive(Command, Debug, Parser, Runnable)]
pub enum ClearCmds {
    /// Clear outstanding packets (i.e., packet-recv and packet-ack)
    /// on a given channel in both directions. The channel is identified
    /// by the chain, port, and channel IDs at one of its ends.
    Packets(ClearPacketsCmd),
}

#[derive(Debug, Parser, Command)]
pub struct ClearPacketsCmd {
    #[clap(
        long = "chain",
        required = true,
        value_name = "CHAIN_ID",
        help = "Identifier of the chain"
    )]
    chain_id: ChainId,

    #[clap(
        long = "port",
        required = true,
        value_name = "PORT_ID",
        help = "Identifier of the port"
    )]
    port_id: PortId,

    #[clap(
        long = "channel",
        alias = "chan",
        required = true,
        value_name = "CHANNEL_ID",
        help = "Identifier of the channel"
    )]
    channel_id: ChannelId,

    #[clap(
        long,
        help = "use the given signing key for the specified chain (default: `key_name` config)"
    )]
    key_name: Option<String>,

    #[clap(
        long,
        help = "use the given signing key for the counterparty chain (default: `counterparty_key_name` config)"
    )]
    counterparty_key_name: Option<String>,
}

impl Override<Config> for ClearPacketsCmd {
    fn override_config(&self, mut config: Config) -> Result<Config, abscissa_core::FrameworkError> {
        let chain_config = config.find_chain_mut(&self.chain_id).ok_or_else(|| {
            FrameworkErrorKind::ComponentError.context(format!(
                "missing configuration for chain '{}'",
                self.chain_id
            ))
        })?;

        if let Some(ref key_name) = self.key_name {
            chain_config.key_name = key_name.to_string();
        }

        Ok(config)
    }
}

impl Runnable for ClearPacketsCmd {
    fn run(&self) {
        let config = app_config();

        let chains = match spawn_chain_counterparty::<BaseChainHandle>(
            &config,
            &self.chain_id,
            &self.port_id,
            &self.channel_id,
        ) {
            Ok((chains, _)) => chains,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        // If `counterparty_key_name` is provided, fetch the counterparty chain's
        // config and overwrite its `key_name` parameter
        if let Some(ref counterparty_key_name) = self.counterparty_key_name {
            match chains.dst.config() {
                Ok(mut dst_chain_cfg) => {
                    dst_chain_cfg.key_name = counterparty_key_name.to_string();
                }
                Err(e) => Output::error(format!("{}", e)).exit(),
            }
        }

        let mut ev_list = vec![];

        // Construct links in both directions.
        let opts = LinkParameters {
            src_port_id: self.port_id.clone(),
            src_channel_id: self.channel_id,
        };
        let fwd_link = match Link::new_from_opts(chains.src.clone(), chains.dst, opts, false) {
            Ok(link) => link,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };
        let rev_link = match fwd_link.reverse(false) {
            Ok(link) => link,
            Err(e) => Output::error(format!("{}", e)).exit(),
        };

        // Schedule RecvPacket messages for pending packets in both directions.
        // This may produce pending acks which will be processed in the next phase.
        run_and_collect_events(&mut ev_list, || {
            fwd_link.relay_recv_packet_and_timeout_messages()
        });
        run_and_collect_events(&mut ev_list, || {
            rev_link.relay_recv_packet_and_timeout_messages()
        });

        // Schedule AckPacket messages in both directions.
        run_and_collect_events(&mut ev_list, || fwd_link.relay_ack_packet_messages());
        run_and_collect_events(&mut ev_list, || rev_link.relay_ack_packet_messages());

        Output::success(ev_list).exit()
    }
}

fn run_and_collect_events<F>(ev_list: &mut Vec<IbcEvent>, f: F)
where
    F: FnOnce() -> Result<Vec<IbcEvent>, LinkError>,
{
    match f() {
        Ok(mut ev) => ev_list.append(&mut ev),
        Err(e) => Output::error(Error::link(e)).exit(),
    };
}
