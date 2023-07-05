use crate::chain::traits::types::ibc::HasIbcChainTypes;
use crate::core::traits::sync::Async;

pub trait HasChannelOpenInitEvent<Counterparty>: HasIbcChainTypes<Counterparty>
where
    Counterparty: HasIbcChainTypes<Self>,
{
    type ChannelOpenInitEvent: Async;

    fn try_extract_channel_open_init_event(
        event: Self::Event,
    ) -> Option<Self::ChannelOpenInitEvent>;

    fn channel_open_init_event_channel_id(event: &Self::ChannelOpenInitEvent) -> &Self::ChannelId;
}
