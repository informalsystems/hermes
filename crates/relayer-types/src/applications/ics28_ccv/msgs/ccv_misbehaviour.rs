use crate::prelude::*;

use ibc_proto::interchain_security::ccv::provider::v1::MsgSubmitConsumerMisbehaviour as RawIcsMisbehaviour;
use ibc_proto::protobuf::Protobuf;
use serde::{Deserialize, Serialize};

use crate::applications::ics28_ccv::msgs::error::Error;
use crate::clients::ics07_tendermint::misbehaviour::Misbehaviour;
use crate::signer::Signer;
use crate::tx_msg::Msg;

pub const ICS_MISBEHAVIOR_TYPE_URL: &str =
    "/interchain_security.ccv.provider.v1.MsgSubmitConsumerMisbehaviour";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MsgSubmitIcsConsumerMisbehaviour {
    pub submitter: Signer,
    pub misbehaviour: Misbehaviour,
}

impl Msg for MsgSubmitIcsConsumerMisbehaviour {
    type ValidationError = crate::core::ics24_host::error::ValidationError;
    type Raw = RawIcsMisbehaviour;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        ICS_MISBEHAVIOR_TYPE_URL.to_string()
    }
}

impl Protobuf<RawIcsMisbehaviour> for MsgSubmitIcsConsumerMisbehaviour {}

impl TryFrom<RawIcsMisbehaviour> for MsgSubmitIcsConsumerMisbehaviour {
    type Error = Error;

    fn try_from(raw: RawIcsMisbehaviour) -> Result<Self, Self::Error> {
        let mis = raw
            .misbehaviour
            .ok_or_else(|| Error::invalid_raw_misbehaviour("missing misbehaviour".into()))?;
        Ok(Self {
            submitter: raw.submitter.parse().map_err(Error::signer)?,
            misbehaviour: mis.try_into().map_err(|_e| {
                Error::invalid_raw_misbehaviour("cannot convert misbehaviour".into())
            })?,
        })
    }
}

impl From<MsgSubmitIcsConsumerMisbehaviour> for RawIcsMisbehaviour {
    fn from(value: MsgSubmitIcsConsumerMisbehaviour) -> Self {
        RawIcsMisbehaviour {
            submitter: value.submitter.to_string(),
            misbehaviour: Some(value.misbehaviour.into()),
        }
    }
}

impl core::fmt::Display for MsgSubmitIcsConsumerMisbehaviour {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(f, "{:?}: {}", self.submitter, self.misbehaviour,)
    }
}
