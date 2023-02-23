use alloc::sync::Arc;

use crate::base::chain::traits::types::event::HasEventType;
use crate::base::chain::traits::types::height::HasHeightType;
use crate::base::runtime::traits::subscription::Subscription;

pub trait HasEventSubscription: HasHeightType + HasEventType {
    fn event_subscription(&self) -> &Arc<dyn Subscription<Item = (Self::Height, Self::Event)>>;
}
