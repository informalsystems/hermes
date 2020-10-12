//! These are definitions of messages that a relayer submits to a chain. Specific implementations of
//! these messages can be found, for instance, in ICS 07 for Tendermint-specific chains. A chain
//! handles these messages in two layers: first with the general ICS 02 client handler, which
//! subsequently calls into the chain-specific (e.g., ICS 07) client handler. See:
//! https://github.com/cosmos/ics/tree/master/spec/ics-002-client-semantics#create.
use std::convert::TryFrom;

use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::error;
use crate::ics24_host::identifier::ClientId;
use crate::tx_msg::Msg;

use ibc_proto::ibc::client::MsgCreateClient as RawMsgCreateClient;
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
    pub client_id: ClientId,
    pub client_type: ClientType,
    pub client_state: AnyClientState,
    pub consensus_state: AnyConsensusState,
    pub signer: AccountId,
}

impl MsgCreateAnyClient {
    pub fn new(
        client_id: ClientId,
        client_type: ClientType,
        client_state: AnyClientState,
        consensus_state: AnyConsensusState,
        signer: AccountId,
    ) -> Self {
        MsgCreateAnyClient {
            client_id,
            client_type,
            client_state,
            consensus_state,
            signer,
        }
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

        let client_type = match raw_client_state.type_url.as_str() {
            "/ibc.tendermint.ClientState" => Ok(ClientType::Tendermint),

            _ => Err(
                Kind::DecodeMessage.context(error::Kind::UnknownConsensusStateType(
                    raw_client_state.clone().type_url,
                )),
            ),
        }?;

        let raw_consensus_state = raw
            .consensus_state
            .ok_or_else(|| Kind::DecodeMessage.context(error::Kind::InvalidRawConsensusState))?;

        Ok(MsgCreateAnyClient {
            client_id: raw.client_id.parse().unwrap(),
            client_type,
            client_state: AnyClientState::try_from(raw_client_state).unwrap(),
            consensus_state: AnyConsensusState::try_from(raw_consensus_state).unwrap(),
            signer: AccountId::from_str(raw.signer.as_str())
                .map_err(|e| Kind::DecodeMessage.context(e))?,
        })
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
    use ibc_proto::ibc::client::MsgCreateClient;
    use std::convert::TryFrom;
    use std::time::Duration;

    use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
    use crate::ics02_client::client_type::ClientType;
    use crate::ics02_client::msgs::MsgCreateAnyClient;
    use crate::ics03_connection::msgs::test_util::get_dummy_account_id;
    use crate::ics07_tendermint::client_state::ClientState;
    use crate::ics07_tendermint::header::test_util::get_dummy_header;
    use crate::ics24_host::identifier::ClientId;
    use tendermint::block::Height;

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
            latest_height: tm_header.signed_header.header.height,
            frozen_height: Height::from(0_u32),
            allow_update_after_expiry: false,
            allow_update_after_misbehaviour: false,
        });

        let msg = MsgCreateAnyClient {
            client_id,
            client_type: ClientType::Tendermint,
            client_state: tm_client_state,
            consensus_state: AnyConsensusState::Tendermint(tm_header.consensus_state()),
            signer,
        };

        let raw = MsgCreateClient::from(msg.clone());
        let msg_back = MsgCreateAnyClient::try_from(raw.clone()).unwrap();
        let raw_back = MsgCreateClient::from(msg_back.clone());
        assert_eq!(msg, msg_back);
        assert_eq!(raw, raw_back);
    }
}
