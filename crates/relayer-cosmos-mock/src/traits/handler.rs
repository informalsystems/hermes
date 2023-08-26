use async_trait::async_trait;
use ibc::core::events::IbcEvent;
use ibc::core::ics23_commitment::commitment::CommitmentProofBytes;
use ibc::core::ics24_host::path::Path;
use ibc::Any;
use ibc::Height;

use crate::types::error::Error;

#[async_trait]
pub trait ChainHandler {
    async fn init(&self);

    async fn begin_block(&self);

    async fn commit(&self);

    async fn run(&self);

    async fn submit_messages(&self, msgs: Vec<Any>) -> Result<Vec<Vec<IbcEvent>>, Error>;

    async fn query(
        &self,
        path: impl Into<Path> + Send,
        height: &Height,
    ) -> Result<(Vec<u8>, CommitmentProofBytes), Error>;
}
