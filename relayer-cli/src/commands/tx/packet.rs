use abscissa_core::{Command, Options, Runnable};

use ibc::events::IBCEvent;
use ibc::ics24_host::identifier::{ChannelId, PortId};
use relayer::config::Config;
use relayer::link::{
    build_and_send_ack_packet_messages, build_and_send_recv_packet_messages, PacketOptions,
};

use crate::conclude::Output;
use crate::error::{Error, Kind};
use crate::prelude::*;

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawPacketRecvCmd {
    #[options(free, help = "identifier of the source chain")]
    src_chain_id: String,

    #[options(free, help = "identifier of the destination chain")]
    dest_chain_id: String,

    #[options(free, help = "identifier of the source port")]
    src_port_id: PortId,

    #[options(free, help = "identifier of the destination port")]
    dst_port_id: PortId,

    #[options(free, help = "identifier of the source channel")]
    src_channel_id: ChannelId,

    #[options(free, help = "identifier of the destination channel")]
    dst_channel_id: ChannelId,
}

impl TxRawPacketRecvCmd {
    fn validate_options(&self, config: &Config) -> Result<PacketOptions, String> {
        let src_chain_config = config
            .find_chain(&self.src_chain_id.parse().unwrap())
            .ok_or_else(|| "missing src chain configuration".to_string())?;

        let dest_chain_config = config
            .find_chain(&self.dest_chain_id.parse().unwrap())
            .ok_or_else(|| "missing destination chain configuration".to_string())?;

        let opts = PacketOptions {
            src_chain_config: src_chain_config.clone(),
            dst_chain_config: dest_chain_config.clone(),
            src_port_id: self.src_port_id.clone(),
            src_channel_id: self.src_channel_id.clone(),
            dst_port_id: self.dst_port_id.clone(),
            dst_channel_id: self.dst_channel_id.clone(),
        };

        Ok(opts)
    }
}

impl Runnable for TxRawPacketRecvCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.validate_options(&config) {
            Err(err) => {
                return Output::error(err).exit();
            }
            Ok(result) => result,
        };
        info!("Message {:?}", opts);

        let res: Result<Vec<IBCEvent>, Error> =
            build_and_send_recv_packet_messages(&opts).map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(ev) => Output::success(ev).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawPacketAckCmd {
    #[options(free, help = "identifier of the source chain")]
    src_chain_id: String,

    #[options(free, help = "identifier of the destination chain")]
    dest_chain_id: String,

    #[options(free, help = "identifier of the source port")]
    src_port_id: PortId,

    #[options(free, help = "identifier of the destination port")]
    dst_port_id: PortId,

    #[options(free, help = "identifier of the source channel")]
    src_channel_id: ChannelId,

    #[options(free, help = "identifier of the destination channel")]
    dst_channel_id: ChannelId,
}

impl TxRawPacketAckCmd {
    fn validate_options(&self, config: &Config) -> Result<PacketOptions, String> {
        let src_chain_config = config
            .find_chain(&self.src_chain_id.parse().unwrap())
            .ok_or_else(|| "missing src chain configuration".to_string())?;

        let dest_chain_config = config
            .find_chain(&self.dest_chain_id.parse().unwrap())
            .ok_or_else(|| "missing destination chain configuration".to_string())?;

        let opts = PacketOptions {
            src_chain_config: src_chain_config.clone(),
            dst_chain_config: dest_chain_config.clone(),
            src_port_id: self.src_port_id.clone(),
            src_channel_id: self.src_channel_id.clone(),
            dst_port_id: self.dst_port_id.clone(),
            dst_channel_id: self.dst_channel_id.clone(),
        };

        Ok(opts)
    }
}

impl Runnable for TxRawPacketAckCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.validate_options(&config) {
            Err(err) => {
                return Output::error(err).exit();
            }
            Ok(result) => result,
        };
        info!("Message {:?}", opts);

        let res: Result<Vec<IBCEvent>, Error> =
            build_and_send_ack_packet_messages(&opts).map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(ev) => Output::success(ev).exit(),
            Err(e) => Output::error(format!("{}", e)).exit(),
        }
    }
}
