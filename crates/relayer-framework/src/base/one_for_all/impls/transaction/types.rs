use crate::base::chain::traits::types::event::HasEventType;
use crate::base::chain::traits::types::message::HasMessageType;
use crate::base::one_for_all::traits::transaction::{OfaTxContext, OfaTxTypes};
use crate::base::one_for_all::types::transaction::OfaTxWrapper;
use crate::base::transaction::traits::types::HasTxTypes;

impl<TxContext> HasMessageType for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxTypes,
{
    type Message = TxContext::Message;
}

impl<TxContext> HasEventType for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxTypes,
{
    type Event = TxContext::Event;
}

impl<TxContext> HasTxTypes for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    type Transaction = TxContext::Transaction;

    type Nonce = TxContext::Nonce;

    type Fee = TxContext::Fee;

    type Signer = TxContext::Signer;

    type TxHash = TxContext::TxHash;

    type TxResponse = TxContext::TxResponse;

    fn tx_size(tx: &Self::Transaction) -> usize {
        TxContext::tx_size(tx)
    }
}
