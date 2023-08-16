use ibc_relayer_components::chain::traits::types::event::HasEventType;
use ibc_relayer_components::chain::traits::types::message::HasMessageType;
use ibc_relayer_components::transaction::traits::types::{HasNonceType, HasSignerType, HasTxTypes};

use crate::one_for_all::traits::transaction::OfaTxContext;
use crate::one_for_all::types::transaction::OfaTxWrapper;

impl<TxContext> HasMessageType for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    type Message = TxContext::Message;
}

impl<TxContext> HasEventType for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    type Event = TxContext::Event;
}

impl<TxContext> HasNonceType for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    type Nonce = TxContext::Nonce;
}

impl<TxContext> HasSignerType for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    type Signer = TxContext::Signer;
}

impl<TxContext> HasTxTypes for OfaTxWrapper<TxContext>
where
    TxContext: OfaTxContext,
{
    type Transaction = TxContext::Transaction;

    type Fee = TxContext::Fee;

    type TxHash = TxContext::TxHash;

    type TxResponse = TxContext::TxResponse;

    fn tx_size(tx: &Self::Transaction) -> usize {
        TxContext::tx_size(tx)
    }
}
