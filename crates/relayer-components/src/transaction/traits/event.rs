use crate::base::transaction::traits::types::HasTxTypes;
use crate::std_prelude::*;

pub trait CanParseTxResponseAsEvents: HasTxTypes {
    fn parse_tx_response_as_events(
        response: Self::TxResponse,
    ) -> Result<Vec<Vec<Self::Event>>, Self::Error>;
}
