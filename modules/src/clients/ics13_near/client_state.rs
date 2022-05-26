use crate::core::{
    ics02_client::{client_state::ClientState, client_type::ClientType},
    ics24_host::identifier::ChainId,
};

use super::types::{CryptoHash, LightClientBlockView, ValidatorStakeView};

#[derive(Debug, Clone)]
pub struct NearClientState {
    chain_id: ChainId,
    head: LightClientBlockView,
    current_epoch: CryptoHash,
    next_epoch: CryptoHash,
    current_validators: Vec<ValidatorStakeView>,
    next_validators: Vec<ValidatorStakeView>,
}

pub struct NearUpgradeOptions {}

impl NearClientState {
    pub fn get_validators_by_epoch(
        &self,
        epoch_id: &CryptoHash,
    ) -> Option<&Vec<ValidatorStakeView>> {
        if epoch_id == &self.current_epoch {
            Some(&self.current_validators)
        } else if epoch_id == &self.next_epoch {
            Some(&self.next_validators)
        } else {
            None
        }
    }

    pub fn get_head(&self) -> &LightClientBlockView {
        &self.head
    }
}

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
