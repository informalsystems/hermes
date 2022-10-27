use async_trait::async_trait;

use crate::base::transaction::traits::types::HasTxTypes;
use crate::std_prelude::*;

#[async_trait]
pub trait CanEncodeTx: HasTxTypes {
    async fn encode_tx(
        &self,
        nonce: &Self::Nonce,
        fee: &Self::Fee,
        messages: &[Self::Message],
    ) -> Result<Self::Transaction, Self::Error>;
}

#[async_trait]
pub trait TxEncoder<Context>
where
    Context: HasTxTypes,
{
    async fn encode_tx(
        context: &Context,
        nonce: &Context::Nonce,
        fee: &Context::Fee,
        messages: &[Context::Message],
    ) -> Result<Context::Transaction, Context::Error>;
}
