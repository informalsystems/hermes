use crate::core::traits::client::HasAnyClientTypes;
use crate::core::traits::event::HasEventTypes;
use crate::core::traits::host::HasHostTypes;
use crate::core::traits::ibc::HasIbcTypes;

pub trait InjectMisbehaviorEvent:
    HasAnyClientTypes + HasEventTypes + HasIbcTypes + HasHostTypes
{
    fn misbehavior_event(
        client_id: &Self::ClientId,
        client_type: &Self::ClientType,
        consensus_height: &Self::Height,
        header: &Self::AnyClientHeader,
    ) -> Self::Event;
}
