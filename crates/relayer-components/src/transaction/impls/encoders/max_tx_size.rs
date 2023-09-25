/*!
   TODO: the max transaction size may not be checked within the transaction
   encoder. Doing so may interfer with the nonce allocator, as it would
   invalidate subsequent nonces that are allocated, since the currently
   allocated nonce is not used.
*/

use core::marker::PhantomData;

use async_trait::async_trait;

use crate::core::traits::error::InjectError;
use crate::std_prelude::*;
use crate::transaction::traits::components::tx_encoder::TxEncoder;
use crate::transaction::traits::types::HasTxTypes;

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
        signer: &Context::Signer,
        nonce: &Context::Nonce,
        fee: &Context::Fee,
        messages: &[Context::Message],
    ) -> Result<Context::Transaction, Context::Error> {
        let tx = InEncoder::encode_tx(context, signer, nonce, fee, messages).await?;

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
