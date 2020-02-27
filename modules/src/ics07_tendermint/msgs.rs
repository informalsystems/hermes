use super::header::Header;
use crate::ics02_client::types::Msg;
use crate::ics24_host::client::ClientId;

use serde_derive::{Deserialize, Serialize};
use tendermint::account::Id as AccountId;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MsgUpdateClient {
    client_id: ClientId,
    header: Header,
    signer: AccountId,
}

impl MsgUpdateClient {
    pub fn new(client_id: ClientId, header: Header, signer: AccountId) -> Self {
        Self {
            client_id,
            header,
            signer,
        }
    }
}

impl Msg for MsgUpdateClient {
    type ValidationError = crate::ics24_host::error::ValidationError;
    type Header = Header;

    fn route(&self) -> String {
        unimplemented!()
    }

    fn get_type(&self) -> String {
        unimplemented!()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        unimplemented!()
    }

    fn get_sign_bytes(&self) -> Vec<u8> {
        unimplemented!()
    }

    fn get_signers(&self) -> Vec<ClientId> {
        unimplemented!()
    }

    fn get_client_id(&self) -> ClientId {
        unimplemented!()
    }

    fn get_header(&self) -> Self::Header {
        unimplemented!()
    }
}

impl crate::ics02_client::types::MsgUpdateClient for MsgUpdateClient {
    fn client_id(&self) -> ClientId {
        self.client_id.clone()
    }

    fn header(&self) -> Self::Header {
        self.header.clone()
    }
}
