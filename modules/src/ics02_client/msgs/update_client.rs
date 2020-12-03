//! These are definitions of messages that a relayer submits to a chain. Specific implementations of
//! these messages can be found, for instance, in ICS 07 for Tendermint-specific chains. A chain
//! handles these messages in two layers: first with the general ICS 02 client handler, which
//! subsequently calls into the chain-specific (e.g., ICS 07) client handler. See:
//! https://github.com/cosmos/ics/tree/master/spec/ics-002-client-semantics#create.

use std::convert::TryFrom;

use tendermint::account::Id as AccountId;
use tendermint_proto::Protobuf;

use ibc_proto::ibc::core::client::v1::MsgUpdateClient as RawMsgUpdateClient;

use crate::address::{account_to_string, string_to_account};
use crate::ics02_client::client_def::AnyHeader;
use crate::ics02_client::error::{Error, Kind};
use crate::ics24_host::identifier::ClientId;
use crate::tx_msg::Msg;

pub const TYPE_URL: &str = "/ibc.core.client.v1.MsgUpdateClient";

/// A type of message that triggers the update of an on-chain (IBC) client with new headers.
#[derive(Clone, Debug, PartialEq)] // TODO: Add Eq bound when possible
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

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        // Nothing to validate since all fields are validated on creation.
        Ok(())
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        vec![self.signer]
    }
}

impl Protobuf<RawMsgUpdateClient> for MsgUpdateAnyClient {}

impl TryFrom<RawMsgUpdateClient> for MsgUpdateAnyClient {
    type Error = Error;

    fn try_from(raw: RawMsgUpdateClient) -> Result<Self, Self::Error> {
        let raw_header = raw.header.ok_or(Kind::InvalidRawHeader)?;
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
    use std::convert::TryFrom;

    use ibc_proto::ibc::core::client::v1::MsgUpdateClient;

    use crate::ics02_client::client_def::AnyHeader;
    use crate::ics02_client::msgs::MsgUpdateAnyClient;
    use crate::ics24_host::identifier::ClientId;

    use crate::ics07_tendermint::header::test_util::get_dummy_ics07_header;
    use crate::test_utils::get_dummy_account_id;

    #[test]
    fn msg_update_client_serialization() {
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
