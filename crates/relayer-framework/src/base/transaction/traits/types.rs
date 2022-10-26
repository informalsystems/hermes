use crate::base::core::traits::error::HasError;

pub trait HasTxTypes: HasError {
    type Message;

    type Transaction;

    type Wallet;

    type Nonce;

    type Fee;

    type Memo;

    type TxHash;

    type TxResponse;
}

pub trait SameTxTypes<Other>:
    HasTxTypes<
    Error = Other::Error,
    Message = Other::Message,
    Transaction = Other::Transaction,
    Wallet = Other::Wallet,
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
        Transaction = Other::Transaction,
        Wallet = Other::Wallet,
        Nonce = Other::Nonce,
        Fee = Other::Fee,
        Memo = Other::Memo,
        TxHash = Other::TxHash,
        TxResponse = Other::TxResponse,
    >,
{
}
