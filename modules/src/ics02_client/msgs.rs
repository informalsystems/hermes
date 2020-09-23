//! These are definitions of messages that a relayer submits to a chain. Specific implementations of
//! these messages can be found, for instance, in ICS 07 for Tendermint-specific chains. A chain
//! handles these messages in two layers: first with the general ICS 02 client handler, which
//! subsequently calls into the chain-specific (e.g., ICS 07) client handler. See:
//! https://github.com/cosmos/ics/tree/master/spec/ics-002-client-semantics#create.

use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
use crate::ics02_client::client_type::ClientType;
use crate::ics02_client::error;
use crate::ics24_host::identifier::ClientId;
use crate::tx_msg::Msg;
use prost_types::Any;
use tendermint::account::Id as AccountId;

use std::convert::TryFrom;
use tendermint_proto::{DomainType, Error, Kind};

pub const TYPE_MSG_CREATE_CLIENT: &str = "create_client";

#[allow(clippy::large_enum_variant)]
pub enum ClientMsg {
    CreateClient(MsgCreateAnyClient),
    UpdateClient(MsgUpdateAnyClient),
}

/// A type of message that triggers the creation of a new on-chain (IBC) client.
#[derive(Clone, Debug, PartialEq)]
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
        let raw_msg: Any = self.clone().into();
        prost::Message::encode(&raw_msg, &mut buf).unwrap();
        buf
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

impl DomainType<Any> for MsgCreateAnyClient {}

impl TryFrom<Any> for MsgCreateAnyClient {
    type Error = Error;

    fn try_from(raw: Any) -> Result<Self, Self::Error> {
        match raw.type_url.as_str() {
            "/ibc.client.MsgCreateClient" => Ok(MsgCreateAnyClient::decode_vec(&raw.value)?),

            _ => Err(Kind::DecodeMessage
                .context(error::Kind::UnknownClientMessageType(raw.type_url))
                .into()),
        }
    }
}

impl From<MsgCreateAnyClient> for Any {
    fn from(value: MsgCreateAnyClient) -> Self {
        let value = value.encode_vec().unwrap();
        Any {
            type_url: "/ibc.client.MsgCreateClient".to_string(),
            value,
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
    use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
    use crate::ics07_tendermint::client_state::ClientState;
    use std::time::Duration;
    use crate::ics07_tendermint::header::test_util::get_dummy_header;
    use std::str::{from_utf8, FromStr};
    use crate::ics03_connection::msgs::test_util::get_dummy_account_id;
    use crate::ics02_client::msgs::MsgCreateAnyClient;
    use crate::ics02_client::client_type::ClientType;
    use prost_types::Any;
    use tendermint::account::Id as AccountId;
    use crate::ics24_host::identifier::ClientId;
    use std::convert::TryFrom;


    #[test]
    fn to_and_from_any() {
        let client_id: ClientId = "tendermint".parse().unwrap();
        let signer = AccountId::from_str(from_utf8(&get_dummy_account_id()).unwrap()).unwrap();
        let tm_header = get_dummy_header();
        let tm_client_state = AnyClientState::Tendermint(ClientState {
            chain_id: tm_header.signed_header.header.chain_id.to_string(),
            trusting_period: Duration::from_secs(64000),
            unbonding_period: Duration::from_secs(128000),
            max_clock_drift: Duration::from_millis(3000),
            latest_height: tm_header.signed_header.header.height,
            frozen_height: 0.into(),
        });

        let msg = MsgCreateAnyClient {
            client_id,
            client_type: ClientType::Tendermint,
            client_state: tm_client_state,
            consensus_state: AnyConsensusState::Tendermint(tm_header.consensus_state()),
            signer,
        };

        let raw = Any::from(msg.clone());
        let msg_back = MsgCreateAnyClient::try_from(raw).unwrap();
        assert_eq!(msg, msg_back);
    }
}