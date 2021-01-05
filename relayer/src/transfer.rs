use crate::chain::{Chain, CosmosSDKChain};
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use ibc::application::ics20_fungible_token_transfer::msgs::transfer::MsgTransfer;
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
    pub amount: u64,
    pub height_offset: u64,
    pub number_msgs: usize,
}

pub fn build_and_send_transfer_messages(
    mut packet_src_chain: CosmosSDKChain, // the chain whose account is debited
    mut packet_dst_chain: CosmosSDKChain, // the chain where the transfer is sent
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
    let msgs = vec![raw_msg; opts.number_msgs];
    Ok(packet_src_chain.send_msgs(msgs)?)
}
