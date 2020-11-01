//! These are definitions of messages that a relayer submits to a chain. Specific implementations of
//! these messages can be found, for instance, in ICS 07 for Tendermint-specific chains. A chain
//! handles these messages in two layers: first with the general ICS 02 client handler, which
//! subsequently calls into the chain-specific (e.g., ICS 07) client handler. See:
//! https://github.com/cosmos/ics/tree/master/spec/ics-002-client-semantics#create.

use std::convert::TryFrom;
use std::str::FromStr;

use tendermint::account::Id as AccountId;
use tendermint_proto::DomainType;

use ibc_proto::ibc::core::client::v1::MsgCreateClient as RawMsgCreateClient;
use ibc_proto::ibc::core::client::v1::MsgUpdateClient as RawMsgUpdateClient;

use crate::address::{account_to_string, string_to_account};
use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
use crate::ics02_client::error;
use crate::ics02_client::error::{Error, Kind};
use crate::ics24_host::identifier::ClientId;
use crate::tx_msg::Msg;

const TYPE_MSG_CREATE_CLIENT: &str = "create_client";
const TYPE_MSG_UPDATE_CLIENT: &str = "update_client";

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
    ) -> Result<Self, Error> {
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

    fn type_url(&self) -> String {
        "/ibc.core.client.v1.MsgCreateClient".to_string()
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
            .ok_or_else(|| Kind::InvalidRawClientState.context("missing client state"))?;

        let raw_consensus_state = raw
            .consensus_state
            .ok_or_else(|| Kind::InvalidRawConsensusState.context("missing consensus state"))?;

        let signer = string_to_account(raw.signer).map_err(|e| Kind::InvalidAddress.context(e))?;

        Ok(MsgCreateAnyClient::new(
            ClientId::from_str(raw.client_id.as_str())
                .map_err(|e| Kind::InvalidIdentifier.context(e))?,
            AnyClientState::try_from(raw_client_state)
                .map_err(|e| Kind::InvalidRawClientState.context(e))?,
            AnyConsensusState::try_from(raw_consensus_state)
                .map_err(|e| Kind::InvalidRawConsensusState.context(e))?,
            signer,
        )?)
    }
}

impl From<MsgCreateAnyClient> for RawMsgCreateClient {
    fn from(ics_msg: MsgCreateAnyClient) -> Self {
        RawMsgCreateClient {
            client_id: ics_msg.client_id.to_string(),
            client_state: Some(ics_msg.client_state.into()),
            consensus_state: Some(ics_msg.consensus_state.into()),
            signer: account_to_string(ics_msg.signer).unwrap(),
        }
    }
}

/// A type of message that triggers the update of an on-chain (IBC) client with new headers.
#[derive(Clone, Debug, PartialEq)]
pub struct MsgUpdateAnyClient {
    pub client_id: ClientId,
    pub header: AnyHeader,
    pub signer: AccountId,
}

impl MsgUpdateAnyClient {
    pub fn new(client_id: ClientId, header: AnyHeader, signer: AccountId) -> Self {
        MsgUpdateAnyClient {
            client_id,
            header,
            signer,
        }
    }
}

impl Msg for MsgUpdateAnyClient {
    type ValidationError = crate::ics24_host::error::ValidationError;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn get_type(&self) -> String {
        TYPE_MSG_UPDATE_CLIENT.to_string()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        // Nothing to validate since all fields are validated on creation.
        Ok(())
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }

    fn type_url(&self) -> String {
        "/ibc.core.client.v1.MsgUpdateClient".to_string()
    }
}

impl DomainType<RawMsgUpdateClient> for MsgUpdateAnyClient {}

impl TryFrom<RawMsgUpdateClient> for MsgUpdateAnyClient {
    type Error = Error;

    fn try_from(raw: RawMsgUpdateClient) -> Result<Self, Self::Error> {
        let raw_header = raw.header.ok_or_else(|| Kind::InvalidRawHeader)?;
        let signer = string_to_account(raw.signer).map_err(|e| Kind::InvalidAddress.context(e))?;

        Ok(MsgUpdateAnyClient {
            client_id: raw.client_id.parse().unwrap(),
            header: AnyHeader::try_from(raw_header).unwrap(),
            signer,
        })
    }
}

impl From<MsgUpdateAnyClient> for RawMsgUpdateClient {
    fn from(ics_msg: MsgUpdateAnyClient) -> Self {
        RawMsgUpdateClient {
            client_id: ics_msg.client_id.to_string(),
            header: Some(ics_msg.header.into()),
            signer: account_to_string(ics_msg.signer).unwrap(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::convert::{TryFrom, TryInto};
    use std::time::Duration;

    use ibc_proto::ibc::core::client::v1::{MsgCreateClient, MsgUpdateClient};
    use tendermint_light_client::types::TrustThreshold;

    use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
    use crate::ics02_client::msgs::{MsgCreateAnyClient, MsgUpdateAnyClient};
    use crate::ics07_tendermint::client_state::ClientState;
    use crate::ics24_host::identifier::ClientId;
    use crate::Height;

    use crate::ics07_tendermint::header::test_util::{
        get_dummy_ics07_header, get_dummy_tendermint_header,
    };
    use crate::test_utils::{default_consensus_params, get_dummy_account_id};

    #[test]
    fn client_state_serialization() {
        let client_id: ClientId = "tendermint".parse().unwrap();
        let signer = get_dummy_account_id();

        let tm_header = get_dummy_tendermint_header();
        let tm_client_state = AnyClientState::Tendermint(ClientState {
            chain_id: tm_header.chain_id.to_string(),
            trust_level: TrustThreshold {
                numerator: 1,
                denominator: 3,
            },
            trusting_period: Duration::from_secs(64000),
            unbonding_period: Duration::from_secs(128000),
            max_clock_drift: Duration::from_millis(3000),
            latest_height: Height::new(0, u64::from(tm_header.height)),
            consensus_params: default_consensus_params(),
            frozen_height: Height::default(),
            allow_update_after_expiry: false,
            allow_update_after_misbehaviour: false,
            upgrade_path: "".to_string(),
        });

        let msg = MsgCreateAnyClient::new(
            client_id,
            tm_client_state,
            AnyConsensusState::Tendermint(tm_header.try_into().unwrap()),
            signer,
        )
        .unwrap();

        let raw = MsgCreateClient::from(msg.clone());
        let msg_back = MsgCreateAnyClient::try_from(raw.clone()).unwrap();
        let raw_back = MsgCreateClient::from(msg_back.clone());
        assert_eq!(msg, msg_back);
        assert_eq!(raw, raw_back);
    }

    #[test]
    fn consensus_state_serialization() {
        let client_id: ClientId = "tendermint".parse().unwrap();
        let signer = get_dummy_account_id();

        let header = get_dummy_ics07_header();

        let msg = MsgUpdateAnyClient::new(client_id, AnyHeader::Tendermint(header), signer);
        let raw = MsgUpdateClient::from(msg.clone());
        let msg_back = MsgUpdateAnyClient::try_from(raw.clone()).unwrap();
        let raw_back = MsgUpdateClient::from(msg_back.clone());
        assert_eq!(msg, msg_back);
        assert_eq!(raw, raw_back);
    }
}
