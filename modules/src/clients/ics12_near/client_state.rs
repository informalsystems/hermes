use crate::core::ics02_client::client_state::ClientState;

#[derive(Debug, Clone)]
pub struct NearClientState {}

struct NearUpgradeOptions {}

impl ClientState for NearClientState {
    fn is_frozen(&self) -> bool {
        self.frozen_height().is_some()
    }

    type UpgradeOptions = NearUpgradeOptions;

    fn chain_id(&self) -> crate::core::ics24_host::identifier::ChainId {
        todo!()
    }

    fn client_type(&self) -> crate::core::ics02_client::client_type::ClientType {
        todo!()
    }

    fn latest_height(&self) -> crate::Height {
        todo!()
    }

    fn frozen_height(&self) -> Option<crate::Height> {
        todo!()
    }

    fn upgrade(
        self,
        upgrade_height: crate::Height,
        upgrade_options: Self::UpgradeOptions,
        chain_id: crate::core::ics24_host::identifier::ChainId,
    ) -> Self {
        todo!()
    }

    fn wrap_any(self) -> crate::core::ics02_client::client_state::AnyClientState {
        todo!()
    }
}
