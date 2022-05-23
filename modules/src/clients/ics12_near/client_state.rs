use crate::core::{
    ics02_client::{client_state::ClientState, client_type::ClientType},
    ics24_host::identifier::ChainId,
};

use super::types::LightClientBlockView;

#[derive(Debug, Clone)]
pub struct NearClientState {
    chain_id: ChainId,
    head: LightClientBlockView,
}

struct NearUpgradeOptions {}

impl ClientState for NearClientState {
    fn is_frozen(&self) -> bool {
        self.frozen_height().is_some()
    }

    type UpgradeOptions = NearUpgradeOptions;

    fn chain_id(&self) -> ChainId {
        self.chain_id.clone()
    }

    fn client_type(&self) -> ClientType {
        ClientType::Near
    }

    fn latest_height(&self) -> crate::Height {
        self.head.get_height()
    }

    fn frozen_height(&self) -> Option<crate::Height> {
        // TODO: validate this
        Some(self.head.get_height())
    }

    fn upgrade(
        self,
        upgrade_height: crate::Height,
        upgrade_options: Self::UpgradeOptions,
        chain_id: ChainId,
    ) -> Self {
        // TODO: validate this -- not sure how to process the given parameters in this case
        self
    }

    fn wrap_any(self) -> crate::core::ics02_client::client_state::AnyClientState {
        todo!()
    }
}
