use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::applications::fee::v1::MsgRegisterCounterpartyAddress;

use crate::applications::ics29_fee::error::Error;
use crate::applications::ics29_fee::utils::encode_message;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::prelude::*;
use crate::signer::Signer;

const TYPE_URL: &str = "/ibc.applications.fee.v1.MsgRegisterCounterpartyAddress";

pub fn build_register_counterparty_address_message(
    address: &Signer,
    counterparty_address: &Signer,
    channel_id: &ChannelId,
    port_id: &PortId,
) -> Result<Any, Error> {
    let message = MsgRegisterCounterpartyAddress {
        address: address.to_string(),
        counterparty_address: counterparty_address.to_string(),
        channel_id: channel_id.to_string(),
        port_id: port_id.to_string(),
    };

    let encoded = encode_message(&message).map_err(Error::encode)?;

    let wrapped = Any {
        type_url: TYPE_URL.to_string(),
        value: encoded,
    };

    Ok(wrapped)
}
