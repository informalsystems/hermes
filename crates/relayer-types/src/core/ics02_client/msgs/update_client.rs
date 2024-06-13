//! Definition of domain type message `MsgUpdateAnyClient`.

use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::client::v1::MsgUpdateClient as RawMsgUpdateClient;
use ibc_proto::Protobuf;

use crate::core::ics02_client::error::Error;
use crate::core::ics24_host::error::ValidationError;
use crate::core::ics24_host::identifier::ClientId;
use crate::signer::Signer;
use crate::tx_msg::Msg;

pub const TYPE_URL: &str = "/ibc.core.client.v1.MsgUpdateClient";

/// A type of message that triggers the update of an on-chain (IBC) client with new headers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MsgUpdateClient {
    pub client_id: ClientId,
    pub header: Any,
    pub signer: Signer,
}

impl MsgUpdateClient {
    pub fn new(client_id: ClientId, header: Any, signer: Signer) -> Self {
        MsgUpdateClient {
            client_id,
            header,
            signer,
        }
    }
}

impl Msg for MsgUpdateClient {
    type ValidationError = ValidationError;
    type Raw = RawMsgUpdateClient;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }
}

impl Protobuf<RawMsgUpdateClient> for MsgUpdateClient {}

impl TryFrom<RawMsgUpdateClient> for MsgUpdateClient {
    type Error = Error;

    fn try_from(raw: RawMsgUpdateClient) -> Result<Self, Self::Error> {
        Ok(MsgUpdateClient {
            client_id: raw
                .client_id
                .parse()
                .map_err(Error::invalid_msg_update_client_id)?,
            header: raw.client_message.ok_or_else(Error::missing_raw_header)?,
            signer: raw.signer.parse().map_err(Error::signer)?,
        })
    }
}

impl From<MsgUpdateClient> for RawMsgUpdateClient {
    fn from(ics_msg: MsgUpdateClient) -> Self {
        RawMsgUpdateClient {
            client_id: ics_msg.client_id.to_string(),
            client_message: Some(ics_msg.header),
            signer: ics_msg.signer.to_string(),
        }
    }
}
