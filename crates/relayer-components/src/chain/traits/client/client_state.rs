use async_trait::async_trait;

use crate::chain::traits::types::client_state::HasClientStateSettingsType;
use crate::std_prelude::*;

#[async_trait]
pub trait CanBuildClientState<Counterparty>: HasClientStateSettingsType<Counterparty> {
    async fn build_client_state(
        &self,
        height: &Self::Height,
        settings: &Self::ClientStateSettings,
    ) -> Self::ClientState;
}
