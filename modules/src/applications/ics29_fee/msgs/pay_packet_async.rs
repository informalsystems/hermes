use ibc_proto::cosmos::base::v1beta1::Coin;
use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::applications::fee::v1::{
    Fee as ProtoFee, MsgPayPacketFeeAsync, PacketFee as ProtoPacketFee,
};
use ibc_proto::ibc::core::channel::v1::PacketId as ProtoPacketId;

use crate::applications::ics29_fee::error::Error;
use crate::applications::ics29_fee::utils::encode_message;
use crate::core::ics04_channel::packet::Sequence;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::prelude::*;
use crate::signer::Signer;

const TYPE_URL: &str = "/ibc.applications.fee.v1.MsgPayPacketFeeAsync";

pub fn build_pay_packet_fee_async_message(
    port_id: &PortId,
    channel_id: &ChannelId,
    sequence: Sequence,
    payer: &Signer,
    recv_fee: Vec<Coin>,
    ack_fee: Vec<Coin>,
    timeout_fee: Vec<Coin>,
) -> Result<Any, Error> {
    let fee = ProtoFee {
        recv_fee,
        ack_fee,
        timeout_fee,
    };

    let packet_fee = ProtoPacketFee {
        fee: Some(fee),
        refund_address: payer.to_string(),
        relayers: Vec::new(),
    };

    let packet_id = ProtoPacketId {
        port_id: port_id.to_string(),
        channel_id: channel_id.to_string(),
        sequence: sequence.into(),
    };

    let message = MsgPayPacketFeeAsync {
        packet_fee: Some(packet_fee),
        packet_id: Some(packet_id),
    };

    let encoded = encode_message(&message).map_err(Error::encode)?;

    Ok(Any {
        type_url: TYPE_URL.to_string(),
        value: encoded,
    })
}
