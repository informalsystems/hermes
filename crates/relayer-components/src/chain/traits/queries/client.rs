use async_trait::async_trait;

use crate::chain::traits::types::client_state::HasClientStateType;
use crate::core::traits::error::HasErrorType;
use crate::std_prelude::*;

#[async_trait]
pub trait CanQueryClientState<Counterparty>:
    HasClientStateType<Counterparty> + HasErrorType
{
    async fn query_connection(
        &self,
        client_id: &Self::ClientId,
        height: &Self::Height,
    ) -> Result<Self::ClientState, Self::Error>;
}
