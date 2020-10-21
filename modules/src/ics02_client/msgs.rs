//! These are definitions of messages that a relayer submits to a chain. Specific implementations of
//! these messages can be found, for instance, in ICS 07 for Tendermint-specific chains. A chain
//! handles these messages in two layers: first with the general ICS 02 client handler, which
//! subsequently calls into the chain-specific (e.g., ICS 07) client handler. See:
//! https://github.com/cosmos/ics/tree/master/spec/ics-002-client-semantics#create.
use std::convert::TryFrom;

use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
use crate::ics02_client::error;
use crate::ics24_host::identifier::ClientId;
use crate::tx_msg::Msg;

use ibc_proto::ibc::core::client::v1::MsgCreateClient as RawMsgCreateClient;
use std::str::FromStr;
use tendermint::account::Id as AccountId;
use tendermint_proto::{DomainType, Error, Kind};

const TYPE_MSG_CREATE_CLIENT: &str = "create_client";

#[allow(clippy::large_enum_variant)]
#[derive(Clone, Debug)]
pub enum ClientMsg {
    CreateClient(MsgCreateAnyClient),
    UpdateClient(MsgUpdateAnyClient),
}

/// A type of message that triggers the creation of a new on-chain (IBC) client.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MsgCreateAnyClient {
    client_id: ClientId,
    client_state: AnyClientState,
    consensus_state: AnyConsensusState,
    signer: AccountId,
}

impl MsgCreateAnyClient {
    pub fn new(
        client_id: ClientId,
        client_state: AnyClientState,
        consensus_state: AnyConsensusState,
        signer: AccountId,
    ) -> Result<Self, error::Error> {
        if client_state.client_type() != consensus_state.client_type() {
            return Err(error::Kind::RawClientAndConsensusStateTypesMismatch {
                state_type: client_state.client_type(),
                consensus_type: consensus_state.client_type(),
            }
            .into());
        }
        Ok(MsgCreateAnyClient {
            client_id,
            client_state,
            consensus_state,
            signer,
        })
    }
    pub fn client_id(&self) -> ClientId {
        self.client_id.clone()
    }
    pub fn client_state(&self) -> AnyClientState {
        self.client_state.clone()
    }
    pub fn consensus_state(&self) -> AnyConsensusState {
        self.consensus_state.clone()
    }
}

impl Msg for MsgCreateAnyClient {
    type ValidationError = crate::ics24_host::error::ValidationError;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_CREATE_CLIENT.to_string()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        // Nothing to validate since all fields are validated on creation.
        Ok(())
    }

    fn get_sign_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        let raw_msg: RawMsgCreateClient = self.clone().into();
        prost::Message::encode(&raw_msg, &mut buf).unwrap();
        buf
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

impl DomainType<RawMsgCreateClient> for MsgCreateAnyClient {}

impl TryFrom<RawMsgCreateClient> for MsgCreateAnyClient {
    type Error = Error;

    fn try_from(raw: RawMsgCreateClient) -> Result<Self, Self::Error> {
        let raw_client_state = raw
            .client_state
            .ok_or_else(|| Kind::DecodeMessage.context(error::Kind::InvalidRawClientState))?;

        let raw_consensus_state = raw
            .consensus_state
            .ok_or_else(|| Kind::DecodeMessage.context(error::Kind::InvalidRawConsensusState))?;

        Ok(MsgCreateAnyClient::new(
            ClientId::from_str(raw.client_id.as_str())
                .map_err(|e| Kind::DecodeMessage.context(e))?,
            AnyClientState::try_from(raw_client_state)
                .map_err(|e| Kind::DecodeMessage.context(e))?,
            AnyConsensusState::try_from(raw_consensus_state)
                .map_err(|e| Kind::DecodeMessage.context(e))?,
            AccountId::from_str(raw.signer.as_str()).map_err(|e| Kind::DecodeMessage.context(e))?,
        )
        .map_err(|e| Kind::DecodeMessage.context(e))?)
    }
}

impl From<MsgCreateAnyClient> for RawMsgCreateClient {
    fn from(ics_msg: MsgCreateAnyClient) -> Self {
        RawMsgCreateClient {
            client_id: ics_msg.client_id.to_string(),
            client_state: Some(ics_msg.client_state.into()),
            consensus_state: Some(ics_msg.consensus_state.into()),
            signer: ics_msg.signer.to_string(),
        }
    }
}

/// A type of message that triggers the update of an on-chain (IBC) client with new headers.
#[derive(Clone, Debug)]
pub struct MsgUpdateAnyClient {
    pub client_id: ClientId,
    pub header: AnyHeader,
    pub signer: AccountId,
}

#[cfg(test)]
mod tests {
    use std::convert::TryFrom;
    use std::time::Duration;

    use ibc_proto::ibc::core::client::v1::MsgCreateClient;

    use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
    use crate::ics02_client::msgs::MsgCreateAnyClient;
    use crate::ics03_connection::msgs::test_util::get_dummy_account_id;
    use crate::ics07_tendermint::client_state::ClientState;
    use crate::ics07_tendermint::header::test_util::get_dummy_header;
    use crate::ics24_host::identifier::ClientId;
    use crate::Height;

    #[test]
    fn to_and_from_any() {
        let client_id: ClientId = "tendermint".parse().unwrap();
        let signer = get_dummy_account_id();

        let tm_header = get_dummy_header();
        let tm_client_state = AnyClientState::Tendermint(ClientState {
            chain_id: tm_header.signed_header.header.chain_id.to_string(),
            trusting_period: Duration::from_secs(64000),
            unbonding_period: Duration::from_secs(128000),
            max_clock_drift: Duration::from_millis(3000),
            latest_height: Height::new(0, u64::from(tm_header.signed_header.header.height)),
            frozen_height: Height::default(),
            allow_update_after_expiry: false,
            allow_update_after_misbehaviour: false,
            upgrade_path: "".to_string(),
        });

        let msg = MsgCreateAnyClient::new(
            client_id,
            tm_client_state,
            AnyConsensusState::Tendermint(tm_header.consensus_state()),
            signer,
        )
        .unwrap();

        let raw = MsgCreateClient::from(msg.clone());
        let msg_back = MsgCreateAnyClient::try_from(raw.clone()).unwrap();
        let raw_back = MsgCreateClient::from(msg_back.clone());
        assert_eq!(msg, msg_back);
        assert_eq!(raw, raw_back);
    }
}
