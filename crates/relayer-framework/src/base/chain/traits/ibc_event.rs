use crate::base::chain::traits::context::{HasChainTypes, HasIbcChainTypes};
use crate::base::core::traits::sync::Async;

pub trait HasIbcEvents<Counterparty>: HasIbcChainTypes<Counterparty>
where
    Counterparty: HasChainTypes,
{
    type WriteAcknowledgementEvent: Async;

    fn try_extract_write_acknowledgement_event(
        event: Self::Event,
    ) -> Option<Self::WriteAcknowledgementEvent>;
}
