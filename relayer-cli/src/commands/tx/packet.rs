use abscissa_core::{Command, FrameworkErrorKind, Options, Runnable};

use ibc::events::IbcEvent;
use ibc::ics24_host::identifier::{ChainId, ChannelId, PortId};
use ibc_relayer::link::{Link, LinkParameters};

use crate::cli_utils::ChainHandlePair;
use crate::conclude::Output;
use crate::config::Config;
use crate::error::{Error, Kind};
use crate::prelude::*;
use abscissa_core::config::Override;

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawPacketRecvCmd {
    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[options(free, required, help = "identifier of the source port")]
    src_port_id: PortId,

    #[options(free, required, help = "identifier of the source channel")]
    src_channel_id: ChannelId,

    #[options(
        help = "use the given signing key (default: `key_name` config)",
        short = "k"
    )]
    key: Option<String>,
}

impl Override<Config> for TxRawPacketRecvCmd {
    fn override_config(&self, mut config: Config) -> Result<Config, abscissa_core::FrameworkError> {
        let src_chain_config = config.find_chain_mut(&self.src_chain_id).ok_or_else(|| {
            FrameworkErrorKind::ComponentError.context("missing src chain configuration")
        })?;

        if let Some(ref key_name) = self.key {
            src_chain_config.key_name = key_name.to_string();
        }

        Ok(config)
    }
}

impl Runnable for TxRawPacketRecvCmd {
    fn run(&self) {
        let config = app_config();

        let chains = match ChainHandlePair::spawn(&config, &self.src_chain_id, &self.dst_chain_id) {
            Ok(chains) => chains,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        let opts = LinkParameters {
            src_port_id: self.src_port_id.clone(),
            src_channel_id: self.src_channel_id.clone(),
        };
        let mut link = match Link::new_from_opts(chains.src, chains.dst, opts) {
            Ok(link) => link,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        let res: Result<Vec<IbcEvent>, Error> = link
            .build_and_send_recv_packet_messages()
            .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(ev) => Output::success(ev).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawPacketAckCmd {
    #[options(free, required, help = "identifier of the destination chain")]
    dst_chain_id: ChainId,

    #[options(free, required, help = "identifier of the source chain")]
    src_chain_id: ChainId,

    #[options(free, required, help = "identifier of the source port")]
    src_port_id: PortId,

    #[options(free, required, help = "identifier of the source channel")]
    src_channel_id: ChannelId,
}

impl Runnable for TxRawPacketAckCmd {
    fn run(&self) {
        let config = app_config();

        let chains = match ChainHandlePair::spawn(&config, &self.src_chain_id, &self.dst_chain_id) {
            Ok(chains) => chains,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        let opts = LinkParameters {
            src_port_id: self.src_port_id.clone(),
            src_channel_id: self.src_channel_id.clone(),
        };
        let mut link = match Link::new_from_opts(chains.src, chains.dst, opts) {
            Ok(link) => link,
            Err(e) => return Output::error(format!("{}", e)).exit(),
        };

        let res: Result<Vec<IbcEvent>, Error> = link
            .build_and_send_ack_packet_messages()
            .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(ev) => Output::success(ev).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
