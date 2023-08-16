use async_trait::async_trait;

use crate::std_prelude::*;
use crate::transaction::traits::types::HasTxTypes;

#[async_trait]
pub trait CanQueryNonce: HasTxTypes {
    async fn query_nonce(&self, signer: &Self::Signer) -> Result<Self::Nonce, Self::Error>;
}
