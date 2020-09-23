use crate::ics07_tendermint::header::Header;
use crate::ics24_host::identifier::ClientId;
use crate::tx_msg::Msg;

use std::time::Duration;

use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use crate::ics02_client::client_type::ClientType;
use crate::ics07_tendermint::client_state::ClientState;
use serde_derive::{Deserialize, Serialize};
use tendermint::account::Id as AccountId;
use crate::try_from_raw::TryFromRaw;
use ibc_proto::ibc::client::MsgCreateClient as RawMsgCreateClient;
use crate::ics07_tendermint::error::{Error, Kind};
use serde_derive::{Deserialize, Serialize};
use std::convert::TryInto;
use std::str::{from_utf8, FromStr};

pub const TYPE_MSG_CREATE_CLIENT: &str = "create_client";

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MsgCreateClient {
    pub client_id: ClientId,
    pub header: Header,
    // trust_level: Fraction,
    pub trusting_period: Duration,
    pub unbonding_period: Duration,
    pub max_clock_drift: Duration,
    // proof_specs: ProofSpecs,
    pub signer: AccountId,
}

impl TryFromRaw for MsgCreateClient {
    type RawType = RawMsgCreateClient;
    type Error = anomaly::Error<Kind>;
    fn try_from(msg: RawMsgCreateClient) -> Result<Self, Self::Error> {
        Ok(Self {
            client_id: msg
                .client_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            client_state: msg
                .client_state
                .map(AnyClientState::from_any)
                .transpose()
                .map_err(|e| Kind::InvalidProof.context(e))?,
            counterparty: msg
                .counterparty
                .ok_or_else(|| Kind::MissingCounterparty)?
                .try_into()?,
            signer: AccountId::from_str(
                from_utf8(&msg.signer).map_err(|e| Kind::InvalidSigner.context(e))?,
            )
                .map_err(|e| Kind::InvalidSigner.context(e))?,
        })
    }
}

impl MsgCreateClient {
    pub fn new(
        client_id: ClientId,
        header: Header,
        // trust_level: Fraction,
        trusting_period: Duration,
        unbonding_period: Duration,
        max_clock_drift: Duration,
        // proof_specs: ProofSpecs,
        signer: AccountId,
    ) -> Self {
        Self {
            client_id,
            header,
            trusting_period,
            unbonding_period,
            max_clock_drift,
            signer,
        }
    }

    pub(crate) fn client_id(&self) -> &ClientId {
        &self.client_id
    }

    pub(crate) fn client_type(&self) -> ClientType {
        ClientType::Tendermint
    }

    pub(crate) fn consensus_state(&self) -> AnyConsensusState {
        AnyConsensusState::Tendermint(self.header.consensus_state())
    }

    pub(crate) fn client_state(&self) -> AnyClientState {
        AnyClientState::Tendermint(ClientState {
            chain_id: self.header.signed_header.header.chain_id.to_string(),
            trusting_period: self.trusting_period,
            unbonding_period: self.unbonding_period,
            max_clock_drift: self.max_clock_drift,
            latest_height: self.header.signed_header.header.height,
            frozen_height: 0.into(),
        })
    }
}

impl Msg for MsgCreateClient {
    type ValidationError = crate::ics24_host::error::ValidationError;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_CREATE_CLIENT.to_string()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        // Nothing to validate since both ClientId and AccountId perform validation on creation.
        Ok(())
    }

    fn get_sign_bytes(&self) -> Vec<u8> {
        todo!()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}
