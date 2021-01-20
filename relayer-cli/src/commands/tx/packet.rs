use abscissa_core::{Command, Options, Runnable};
use serde_json::json;

use ibc::events::IBCEvent;
use ibc::ics24_host::identifier::{ChannelId, ClientId, PortId};
use relayer::chain::runtime::ChainRuntime;
use relayer::chain::CosmosSDKChain;
use relayer::config::Config;
use relayer::link::{
    build_and_send_ack_packet_messages, build_and_send_recv_packet_messages, PacketEnvelope,
    PacketOptions,
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

    #[options(free, help = "identifier of the source client")]
    src_client_id: ClientId,

    #[options(free, help = "identifier of the destination client")]
    dest_client_id: ClientId,

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
            packet_src_chain_config: src_chain_config.clone(),
            packet_dst_chain_config: dest_chain_config.clone(),
            packet_envelope: PacketEnvelope {
                packet_src_client_id: self.src_client_id.clone(),
                packet_src_port_id: self.src_port_id.clone(),
                packet_src_channel_id: self.src_channel_id.clone(),
                packet_dst_client_id: self.dest_client_id.clone(),
                packet_dst_port_id: self.dst_port_id.clone(),
                packet_dst_channel_id: self.dst_channel_id.clone(),
            },
        };

        Ok(opts)
    }
}

impl Runnable for TxRawPacketRecvCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.validate_options(&config) {
            Err(err) => {
                return Output::with_error().with_result(json!(err)).exit();
            }
            Ok(result) => result,
        };
        info!("Message {:?}", opts);

        let src_chain_res =
            ChainRuntime::<CosmosSDKChain>::spawn(opts.packet_src_chain_config.clone())
                .map_err(|e| Kind::Runtime.context(e));
        let src_chain = match src_chain_res {
            Ok((handle, _)) => handle,
            Err(e) => {
                return Output::with_error()
                    .with_result(json!(format!("{}", e)))
                    .exit();
            }
        };

        let dst_chain_res =
            ChainRuntime::<CosmosSDKChain>::spawn(opts.packet_dst_chain_config.clone())
                .map_err(|e| Kind::Runtime.context(e));
        let dst_chain = match dst_chain_res {
            Ok((handle, _)) => handle,
            Err(e) => {
                return Output::with_error()
                    .with_result(json!(format!("{}", e)))
                    .exit();
            }
        };

        let res: Result<Vec<IBCEvent>, Error> =
            build_and_send_recv_packet_messages(src_chain, dst_chain, &opts)
                .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(ev) => Output::with_success().with_result(json!(ev)).exit(),
            Err(e) => Output::with_error()
                .with_result(json!(format!("{}", e)))
                .exit(),
        }
    }
}

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawPacketAckCmd {
    #[options(free, help = "identifier of the source chain")]
    src_chain_id: String,

    #[options(free, help = "identifier of the destination chain")]
    dest_chain_id: String,

    #[options(free, help = "identifier of the source client")]
    src_client_id: ClientId,

    #[options(free, help = "identifier of the destination client")]
    dest_client_id: ClientId,

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
            packet_src_chain_config: src_chain_config.clone(),
            packet_dst_chain_config: dest_chain_config.clone(),
            packet_envelope: PacketEnvelope {
                packet_src_client_id: self.src_client_id.clone(),
                packet_src_port_id: self.src_port_id.clone(),
                packet_src_channel_id: self.src_channel_id.clone(),
                packet_dst_client_id: self.dest_client_id.clone(),
                packet_dst_port_id: self.dst_port_id.clone(),
                packet_dst_channel_id: self.dst_channel_id.clone(),
            },
        };

        Ok(opts)
    }
}

impl Runnable for TxRawPacketAckCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.validate_options(&config) {
            Err(err) => {
                return Output::with_error().with_result(json!(err)).exit();
            }
            Ok(result) => result,
        };
        info!("Message {:?}", opts);

        let src_chain_res =
            ChainRuntime::<CosmosSDKChain>::spawn(opts.packet_src_chain_config.clone())
                .map_err(|e| Kind::Runtime.context(e));
        let src_chain = match src_chain_res {
            Ok((handle, _)) => handle,
            Err(e) => {
                return Output::with_error()
                    .with_result(json!(format!("{}", e)))
                    .exit();
            }
        };

        let dst_chain_res =
            ChainRuntime::<CosmosSDKChain>::spawn(opts.packet_dst_chain_config.clone())
                .map_err(|e| Kind::Runtime.context(e));
        let dst_chain = match dst_chain_res {
            Ok((handle, _)) => handle,
            Err(e) => {
                return Output::with_error()
                    .with_result(json!(format!("{}", e)))
                    .exit();
            }
        };

        let res: Result<Vec<IBCEvent>, Error> =
            build_and_send_ack_packet_messages(src_chain, dst_chain, &opts)
                .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(ev) => Output::with_success().with_result(json!(ev)).exit(),
            Err(e) => Output::with_error()
                .with_result(json!(format!("{}", e)))
                .exit(),
        }
    }
}
