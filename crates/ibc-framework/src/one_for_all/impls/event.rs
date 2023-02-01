use crate::core::traits::events::misbehavior::InjectMisbehaviorEvent;
use crate::core::traits::events::update_client::InjectUpdateClientEvent;
use crate::one_for_all::traits::chain::OfaChain;
use crate::one_for_all::types::chain::OfaChainWrapper;

impl<Chain> InjectUpdateClientEvent for OfaChainWrapper<Chain>
where
    Chain: OfaChain,
{
    fn update_client_event(
        client_id: &Self::ClientId,
        client_type: &Self::ClientType,
        consensus_height: &Self::Height,
        header: &Self::AnyClientHeader,
    ) -> Self::Event {
        Chain::update_client_event(client_id, client_type, consensus_height, header)
    }
}

impl<Chain> InjectMisbehaviorEvent for OfaChainWrapper<Chain>
where
    Chain: OfaChain,
{
    fn misbehavior_event(
        client_id: &Self::ClientId,
        client_type: &Self::ClientType,
        consensus_height: &Self::Height,
        header: &Self::AnyClientHeader,
    ) -> Self::Event {
        Chain::misbehavior_event(client_id, client_type, consensus_height, header)
    }
}
