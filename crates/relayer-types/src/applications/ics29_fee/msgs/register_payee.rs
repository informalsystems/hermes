use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::applications::fee::v1::{MsgRegisterCounterpartyPayee, MsgRegisterPayee};

use crate::applications::ics29_fee::error::Error;
use crate::core::ics24_host::identifier::{ChannelId, PortId};
use crate::prelude::*;
use crate::signer::Signer;
use crate::tx_msg::encode_message;

pub fn build_register_counterparty_payee_message(
    address: &Signer,
    counterparty_payee: &Signer,
    channel_id: &ChannelId,
    port_id: &PortId,
) -> Result<Any, Error> {
    const TYPE_URL: &str = "/ibc.applications.fee.v1.MsgRegisterCounterpartyPayee";

    let message = MsgRegisterCounterpartyPayee {
        relayer: address.to_string(),
        counterparty_payee: counterparty_payee.to_string(),
        channel_id: channel_id.to_string(),
        port_id: port_id.to_string(),
    };

    let encoded = encode_message(&message).map_err(Error::encode)?;

    Ok(Any {
        type_url: TYPE_URL.to_string(),
        value: encoded,
    })
}

pub fn build_register_payee_message(
    address: &Signer,
    payee: &Signer,
    channel_id: &ChannelId,
    port_id: &PortId,
) -> Result<Any, Error> {
    const TYPE_URL: &str = "/ibc.applications.fee.v1.MsgRegisterPayee";

    let message = MsgRegisterPayee {
        relayer: address.to_string(),
        payee: payee.to_string(),
        channel_id: channel_id.to_string(),
        port_id: port_id.to_string(),
    };

    let encoded = encode_message(&message).map_err(Error::encode)?;

    Ok(Any {
        type_url: TYPE_URL.to_string(),
        value: encoded,
    })
}
