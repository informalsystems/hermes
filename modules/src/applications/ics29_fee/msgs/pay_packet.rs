use ibc_proto::cosmos::base::v1beta1::Coin;
use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::applications::fee::v1::{Fee as ProtoFee, MsgPayPacketFee};

use crate::applications::ics29_fee::error::Error;
use crate::applications::ics29_fee::utils::encode_message;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::prelude::*;
use crate::signer::Signer;

const TYPE_URL: &str = "/ibc.applications.fee.v1.MsgPayPacketFee";

pub fn build_pay_packet_message(
    port_id: &PortId,
    channel_id: &ChannelId,
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
