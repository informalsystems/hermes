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

#[cfg(test)]
pub mod test_util {
    use crate::ics07_tendermint::header::Header;
    use subtle_encoding::hex;
    use tendermint::block::signed_header::SignedHeader;
    use tendermint::validator::Info as ValidatorInfo;
    use tendermint::validator::Set as ValidatorSet;
    use tendermint::{vote, PublicKey};

    // TODO: This should be replaced with a ::default() or ::produce().
    // The implementation of this function comprises duplicate code (code borrowed from
    // `tendermint-rs` for assembling a Header).
    // See https://github.com/informalsystems/tendermint-rs/issues/381.
    pub fn get_dummy_header() -> Header {
        // Build a SignedHeader from a JSON file.
        let shdr = serde_json::from_str::<SignedHeader>(include_str!(
            "../../tests/support/signed_header.json"
        ))
        .unwrap();

        // Build a set of validators.
        // Below are test values inspired form `test_validator_set()` in tendermint-rs.
        let v1: ValidatorInfo = ValidatorInfo::new(
            PublicKey::from_raw_ed25519(
                &hex::decode_upper(
                    "F349539C7E5EF7C49549B09C4BFC2335318AB0FE51FBFAA2433B4F13E816F4A7",
                )
                .unwrap(),
            )
            .unwrap(),
            vote::Power::new(281_815),
        );

        let vs = ValidatorSet::new(vec![v1]);

        Header {
            signed_header: shdr,
            validator_set: vs.clone(),
            next_validator_set: vs.clone(),
        }
    }
}
