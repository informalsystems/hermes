use ibc_proto::{
    google::protobuf::Any as ProtoAny,
    ibc::core::client::v1::MsgSubmitMisbehaviour as RawMsgSubmitMisbehaviour,
    Protobuf,
};

use crate::{
    core::{
        ics02_client::error::Error,
        ics24_host::identifier::ClientId,
    },
    signer::Signer,
    tx_msg::Msg,
};

pub const TYPE_URL: &str = "/ibc.core.client.v1.MsgSubmitMisbehaviour";

/// A type of message that submits client misbehaviour proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MsgSubmitMisbehaviour {
    /// client unique identifier
    pub client_id: ClientId,
    /// misbehaviour used for freezing the light client
    pub misbehaviour: ProtoAny,
    /// signer address
    pub signer: Signer,
}

impl Msg for MsgSubmitMisbehaviour {
    type ValidationError = crate::core::ics24_host::error::ValidationError;
    type Raw = RawMsgSubmitMisbehaviour;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }
}

impl Protobuf<RawMsgSubmitMisbehaviour> for MsgSubmitMisbehaviour {}

impl TryFrom<RawMsgSubmitMisbehaviour> for MsgSubmitMisbehaviour {
    type Error = Error;

    // NOTE: The `MsgSubmitMisbehaviour` message has been deprecated in IBC-Go v7 in favor of a
    // regular `MsgUpdateClient`, but will keep working for the foreseeable future.
    #[allow(deprecated)]
    fn try_from(raw: RawMsgSubmitMisbehaviour) -> Result<Self, Self::Error> {
        Ok(MsgSubmitMisbehaviour {
            client_id: raw
                .client_id
                .parse()
                .map_err(Error::invalid_raw_misbehaviour)?,
            misbehaviour: raw
                .misbehaviour
                .ok_or_else(Error::missing_raw_misbehaviour)?,
            signer: raw.signer.parse().map_err(Error::signer)?,
        })
    }
}

impl From<MsgSubmitMisbehaviour> for RawMsgSubmitMisbehaviour {
    // NOTE: The `MsgSubmitMisbehaviour` message has been deprecated in IBC-Go v7 in favor of a
    // regular `MsgUpdateClient`, but will keep working for the foreseeable future.
    #[allow(deprecated)]
    fn from(ics_msg: MsgSubmitMisbehaviour) -> Self {
        RawMsgSubmitMisbehaviour {
            client_id: ics_msg.client_id.to_string(),
            misbehaviour: Some(ics_msg.misbehaviour),
            signer: ics_msg.signer.to_string(),
        }
    }
}
