use serde_derive::{Deserialize, Serialize};

// use tendermint::lite::types::SignedHeader;
use tendermint::block::signed_header::SignedHeader;
use tendermint::validator::Set as ValidatorSet;

/// Tendermint consensus header
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Header {
    signed_header: SignedHeader,
    validator_set: ValidatorSet,
    next_validator_set: ValidatorSet,
}

impl tendermint::lite::Header for Header {
    type Time = std::time::SystemTime;
    fn height(&self) -> u64 {
        unimplemented!()
    }
    fn bft_time(&self) -> Self::Time {
        unimplemented!()
    }
    fn validators_hash(&self) -> tendermint::hash::Hash {
        unimplemented!()
    }
    fn next_validators_hash(&self) -> tendermint::hash::Hash {
        unimplemented!()
    }
    fn hash(&self) -> tendermint::hash::Hash {
        unimplemented!()
    }
}
