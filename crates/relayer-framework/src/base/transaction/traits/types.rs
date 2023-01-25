use crate::base::chain::traits::types::event::HasEventType;
use crate::base::chain::traits::types::message::HasMessageType;
use crate::base::core::traits::error::HasErrorType;
use crate::base::core::traits::sync::Async;

pub trait HasTxTypes: HasMessageType + HasEventType + HasErrorType {
    type Transaction: Async;

    type Nonce: Async;

    type Fee: Async;

    type Signer: Async;

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
    Signer = Other::Signer,
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
        Signer = Other::Signer,
        TxHash = Other::TxHash,
        TxResponse = Other::TxResponse,
    >,
{
}
