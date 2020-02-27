use serde_derive::{Deserialize, Serialize};

// use tendermint::lite::types::SignedHeader;
use tendermint::block::signed_header::SignedHeader;
use tendermint::validator::Set as ValidatorSet;

use crate::ics02_client::client_type::ClientType;
use crate::Height;

/// Tendermint consensus header
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Header {
    pub signed_header: SignedHeader,
    pub validator_set: ValidatorSet,
    pub next_validator_set: ValidatorSet,
}

impl crate::ics02_client::header::Header for Header {
    fn client_type(&self) -> ClientType {
        ClientType::Tendermint
    }

    fn height(&self) -> Height {
        use tendermint::lite::types::Header;
        self.signed_header.header.height()
    }
}
