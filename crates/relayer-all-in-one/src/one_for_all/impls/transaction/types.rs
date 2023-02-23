use crate::one_for_all::traits::transaction::{OfaTxContext, OfaTxTypes};
use crate::one_for_all::types::transaction::OfaTxWrapper;
use ibc_relayer_components::chain::traits::types::event::HasEventType;
use ibc_relayer_components::chain::traits::types::message::HasMessageType;
use ibc_relayer_components::transaction::traits::types::HasTxTypes;

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
