use core::fmt;

use ibc_proto::{
    interchain_security::ccv::provider::v1::MsgSubmitConsumerDoubleVoting as RawIcsDoubleVoting,
    Protobuf,
};
use tendermint::evidence::DuplicateVoteEvidence;

use super::error::Error;
use crate::{
    clients::ics07_tendermint::header::Header,
    signer::Signer,
    tx_msg::Msg,
};

pub const ICS_DOUBLE_VOTING_TYPE_URL: &str =
    "/interchain_security.ccv.provider.v1.MsgSubmitConsumerDoubleVoting";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MsgSubmitIcsConsumerDoubleVoting {
    pub submitter: Signer,
    pub duplicate_vote_evidence: DuplicateVoteEvidence,
    pub infraction_block_header: Header,
}

impl Msg for MsgSubmitIcsConsumerDoubleVoting {
    type ValidationError = crate::core::ics24_host::error::ValidationError;
    type Raw = RawIcsDoubleVoting;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        ICS_DOUBLE_VOTING_TYPE_URL.to_string()
    }
}

impl Protobuf<RawIcsDoubleVoting> for MsgSubmitIcsConsumerDoubleVoting {}

impl TryFrom<RawIcsDoubleVoting> for MsgSubmitIcsConsumerDoubleVoting {
    type Error = Error;

    fn try_from(raw: RawIcsDoubleVoting) -> Result<Self, Self::Error> {
        Ok(Self {
            submitter: raw.submitter.parse().map_err(Error::signer)?,
            duplicate_vote_evidence: raw
                .duplicate_vote_evidence
                .ok_or_else(|| Error::invalid_raw_double_voting("missing evidence".into()))?
                .try_into()
                .map_err(|e| {
                    Error::invalid_raw_double_voting(format!("cannot convert evidence: {e}"))
                })?,
            infraction_block_header: raw
                .infraction_block_header
                .ok_or_else(|| {
                    Error::invalid_raw_double_voting("missing infraction block header".into())
                })?
                .try_into()
                .map_err(|e| {
                    Error::invalid_raw_double_voting(format!("cannot convert header: {e}"))
                })?,
        })
    }
}

impl From<MsgSubmitIcsConsumerDoubleVoting> for RawIcsDoubleVoting {
    fn from(value: MsgSubmitIcsConsumerDoubleVoting) -> Self {
        RawIcsDoubleVoting {
            submitter: value.submitter.to_string(),
            duplicate_vote_evidence: Some(value.duplicate_vote_evidence.into()),
            infraction_block_header: Some(value.infraction_block_header.into()),
        }
    }
}

impl fmt::Display for MsgSubmitIcsConsumerDoubleVoting {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("MsgSubmitIcsConsumerDoubleVoting")
            .field("submitter", &self.submitter)
            .field("duplicate_vote_evidence", &"[...]")
            .field(
                "infraction_block_header",
                &self.infraction_block_header.signed_header.header.height,
            )
            .finish()
    }
}
