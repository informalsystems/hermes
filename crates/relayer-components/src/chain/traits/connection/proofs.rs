use async_trait::async_trait;

use crate::chain::traits::types::commitment::HasCommitmentProofsType;
use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildConnectionProofs<Counterparty>:
    HasIbcChainTypes<Counterparty> + HasCommitmentProofsType<Counterparty> + HasErrorType
{
    async fn build_connection_proofs(
        &self,
        connection_id: &Self::ConnectionId,
        height: &Self::Height,
    ) -> Result<Self::CommitmentProofs, Self::Error>;
}
