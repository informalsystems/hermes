use async_trait::async_trait;
use core::marker::PhantomData;

use crate::base::core::traits::error::InjectError;
use crate::base::transaction::traits::encode::TxEncoder;
use crate::base::transaction::traits::types::HasTxTypes;
use crate::std_prelude::*;

pub struct MaxTxSizeExceededError {
    pub max_tx_size: usize,
    pub given_tx_size: usize,
}

pub trait HasMaxTxSizeExceededError: InjectError<MaxTxSizeExceededError> {
    fn try_extract_max_tx_size_exceeded_error(e: Self::Error) -> Option<MaxTxSizeExceededError>;
}

pub trait HasMaxTxSize {
    fn max_tx_size(&self) -> usize;
}

pub struct CheckEncodedTxSize<InEncoder>(PhantomData<InEncoder>);

#[async_trait]
impl<Context, InEncoder> TxEncoder<Context> for CheckEncodedTxSize<InEncoder>
where
    Context: HasTxTypes + HasMaxTxSize + HasMaxTxSizeExceededError,
    InEncoder: TxEncoder<Context>,
{
    async fn encode_tx(
        context: &Context,
        nonce: &Context::Nonce,
        fee: &Context::Fee,
        messages: &[Context::Message],
    ) -> Result<Context::Transaction, Context::Error> {
        let tx = InEncoder::encode_tx(context, nonce, fee, messages).await?;

        let given_tx_size = Context::tx_size(&tx);
        let max_tx_size = context.max_tx_size();

        if given_tx_size > max_tx_size {
            Err(Context::inject_error(MaxTxSizeExceededError {
                given_tx_size,
                max_tx_size,
            }))
        } else {
            Ok(tx)
        }
    }
}
