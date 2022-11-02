use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::applications::fee::v1::{Fee as ProtoFee, MsgPayPacketFee};

use crate::applications::ics29_fee::error::Error;
use crate::applications::transfer::coin::RawCoin;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::prelude::*;
use crate::signer::Signer;
use crate::tx_msg::encode_message;

const TYPE_URL: &str = "/ibc.applications.fee.v1.MsgPayPacketFee";

pub fn build_pay_packet_message(
    port_id: &PortId,
    channel_id: &ChannelId,
    payer: &Signer,
    recv_fee: Vec<RawCoin>,
    ack_fee: Vec<RawCoin>,
    timeout_fee: Vec<RawCoin>,
) -> Result<Any, Error> {
    let fee = ProtoFee {
        recv_fee: recv_fee.into_iter().map(Into::into).collect(),
        ack_fee: ack_fee.into_iter().map(Into::into).collect(),
        timeout_fee: timeout_fee.into_iter().map(Into::into).collect(),
    };

    let message = MsgPayPacketFee {
        fee: Some(fee),
        source_port_id: port_id.to_string(),
        source_channel_id: channel_id.to_string(),
        signer: payer.to_string(),
        relayers: Vec::new(),
    };

    let encoded = encode_message(&message).map_err(Error::encode)?;

    Ok(Any {
        type_url: TYPE_URL.to_string(),
        value: encoded,
    })
}
