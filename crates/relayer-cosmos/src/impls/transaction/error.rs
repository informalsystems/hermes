use ibc_relayer_components::transaction::components::poll::InjectNoTxResponseError;
use tendermint::Hash as TxHash;

use crate::contexts::transaction::CosmosTxContext;
use crate::types::error::{BaseError, Error};

impl InjectNoTxResponseError for CosmosTxContext {
    fn tx_no_response_error(tx_hash: &TxHash) -> Error {
        BaseError::tx_no_response(*tx_hash).into()
    }
}
