use crate::chain::{Chain, CosmosSDKChain};
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use ibc::application::msgs::transfer::MsgTransfer;
use ibc::events::IBCEvent;
use ibc::ics24_host::identifier::{ChannelId, PortId};
use ibc::tx_msg::Msg;
use ibc_proto::ibc::applications::transfer::v1::MsgTransfer as RawMsgTransfer;

#[derive(Clone, Debug)]
pub struct TransferOptions {
    pub packet_src_chain_config: ChainConfig,
    pub packet_dst_chain_config: ChainConfig,
    pub packet_src_port_id: PortId,
    pub packet_src_channel_id: ChannelId,
    pub amount: String,
    pub height_offset: u64,
}

pub fn build_and_send_send_packet_messages(
    mut packet_src_chain: CosmosSDKChain, // the chain where the transfer is sent
    mut packet_dst_chain: CosmosSDKChain, // the chain from whose account the amount is debited
    opts: &TransferOptions,
) -> Result<Vec<IBCEvent>, Error> {
    let receiver = packet_dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    let sender = packet_src_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    let latest_height = packet_dst_chain.query_latest_height()?;

    // TODO - send multiple messages
    let msg = MsgTransfer {
        source_port: opts.packet_src_port_id.clone(),
        source_channel: opts.packet_src_channel_id.clone(),
        token: Some(ibc_proto::cosmos::base::v1beta1::Coin {
            denom: "samoleans".to_string(),
            amount: opts.amount.to_string(),
        }),
        sender,
        receiver,
        timeout_height: latest_height.add(opts.height_offset),
        timeout_timestamp: 0,
    };

    let raw_msg = msg.to_any::<RawMsgTransfer>();
    let mut msgs = vec![];
    msgs.append(&mut vec![raw_msg]);
    Ok(packet_src_chain.send_msgs(msgs)?)
}
