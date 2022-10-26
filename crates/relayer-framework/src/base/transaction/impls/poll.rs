use async_trait::async_trait;
use core::marker::PhantomData;

use crate::base::transaction::traits::response::TxResponseQuerier;
use crate::base::transaction::traits::types::HasTxTypes;
use crate::std_prelude::*;

pub struct PollTxResponse<InQuerier>(pub PhantomData<InQuerier>);

#[async_trait]
impl<Context, InQuerier> TxResponseQuerier<Context> for PollTxResponse<InQuerier>
where
    Context: HasTxTypes,
    InQuerier: TxResponseQuerier<Context>,
{
    async fn query_tx_response(
        _context: &Context,
        _tx_hash: &Context::TxHash,
    ) -> Result<Option<Context::TxResponse>, Context::Error> {
        todo!()
    }
}
