use crate::base::chain::traits::types::{HasEventType, HasMessageType};
use crate::base::core::traits::error::HasError;
use crate::base::core::traits::sync::Async;

pub trait HasTxTypes: HasMessageType + HasEventType + HasError {
    type Transaction: Async;

    type Nonce: Async;

    type Fee: Async;

    type Memo: Async;

    type TxHash: Async;

    type TxResponse: Async;

    fn tx_size(tx: &Self::Transaction) -> usize;
}

pub trait SameTxTypes<Other>:
    HasTxTypes<
    Error = Other::Error,
    Message = Other::Message,
    Event = Other::Event,
    Transaction = Other::Transaction,
    Nonce = Other::Nonce,
    Fee = Other::Fee,
    Memo = Other::Memo,
    TxHash = Other::TxHash,
    TxResponse = Other::TxResponse,
>
where
    Other: HasTxTypes,
{
}

impl<Context, Other> SameTxTypes<Other> for Context
where
    Other: HasTxTypes,
    Context: HasTxTypes<
        Error = Other::Error,
        Message = Other::Message,
        Event = Other::Event,
        Transaction = Other::Transaction,
        Nonce = Other::Nonce,
        Fee = Other::Fee,
        Memo = Other::Memo,
        TxHash = Other::TxHash,
        TxResponse = Other::TxResponse,
    >,
{
}
