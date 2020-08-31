use tendermint::account::Id as AccountId;
use tendermint::chain::Id as ChainId;
use tendermint::block::Height;
use ibc_proto::tx::v1beta1::{Fee, Tx};
use anomaly::Error;
use tendermint::Kind;

pub trait Msg {
    type ValidationError: std::error::Error;

    fn route(&self) -> String;

    fn get_type(&self) -> String;

    fn validate_basic(&self) -> Result<(), Self::ValidationError>;

    fn get_sign_bytes(&self) -> Vec<u8>;

    fn get_signers(&self) -> Vec<AccountId>;
}

pub struct StdSignMsg {
    chain_id: ChainId,
    account: AccountId,
    timeout_height: Height,
    msgs: Vec<dyn Msg>,
    memo: String,
    fee: Fee,
    sequence: Sequence
}

trait Builder {
    fn newBuilder() -> Tx {
    }
}

pub fn get_bytes(tx: &Tx) -> Result<Vec<u8>, Error<Kind>> {
    match tx.body {
        Some(b) => {

        }
        None => {

        }
    }
}
