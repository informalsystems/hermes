use crate::prelude::*;

use abscissa_core::{Command, Options, Runnable};
use relayer::config::Config;

use crate::error::{Error, Kind};
use ibc::ics24_host::identifier::{ChannelId, ClientId, PortId};
use relayer::chain::runtime::ChainRuntime;
use relayer::link::{build_packet_recv_and_send, PacketOptions};

#[derive(Clone, Command, Debug, Options)]
pub struct TxRawPacketRecvCmd {
    #[options(free, help = "identifier of the destination chain")]
    dest_chain_id: String,

    #[options(free, help = "identifier of the destination client")]
    dest_client_id: ClientId,

    #[options(free, help = "identifier of the source chain")]
    src_chain_id: String,

    #[options(free, help = "identifier of the source port")]
    src_port_id: PortId,

    #[options(free, help = "identifier of the source channel")]
    src_channel_id: ChannelId,
}

impl TxRawPacketRecvCmd {
    fn validate_options(&self, config: &Config) -> Result<PacketOptions, String> {
        let dest_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == self.dest_chain_id.parse().unwrap())
            .ok_or_else(|| "missing destination chain configuration".to_string())?;

        let src_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == self.src_chain_id.parse().unwrap())
            .ok_or_else(|| "missing src chain configuration".to_string())?;

        let opts = PacketOptions {
            dst_chain_config: dest_chain_config.clone(),
            src_chain_config: src_chain_config.clone(),
            dst_client_id: self.dest_client_id.clone(),
            src_port_id: self.src_port_id.clone(),
            src_channel_id: self.src_channel_id.clone(),
        };

        Ok(opts)
    }
}

impl Runnable for TxRawPacketRecvCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.validate_options(&config) {
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(result) => result,
        };
        status_info!("Message", "{:?}", opts);

        let (src_chain, _) = ChainRuntime::spawn(opts.src_chain_config.clone()).unwrap();
        let (dst_chain, _) = ChainRuntime::spawn(opts.dst_chain_config.clone()).unwrap();

        let res: Result<Vec<String>, Error> =
            build_packet_recv_and_send(dst_chain, src_chain, &opts)
                .map_err(|e| Kind::Tx.context(e).into());

        match res {
            Ok(receipt) => status_info!("packet recv, result: ", "{:?}", &receipt[0]),
            Err(e) => status_info!("packet recv failed, error: ", "{}", e),
        }
    }
}
