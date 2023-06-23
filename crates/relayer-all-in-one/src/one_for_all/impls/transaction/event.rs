use ibc_relayer_components::transaction::traits::event::CanParseTxResponseAsEvents;

use crate::base::one_for_all::traits::transaction::OfaTxContext;
use crate::base::one_for_all::types::transaction::OfaTxWrapper;
use crate::std_prelude::*;

impl<TxContext> CanParseTxResponseAsEvents for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    fn parse_tx_response_as_events(
        response: Self::TxResponse,
    ) -> Result<Vec<Vec<Self::Event>>, Self::Error> {
        TxContext::parse_tx_response_as_events(response)
    }
}
