use crate::base::chain::traits::context::{ChainContext, IbcChainContext};
use crate::base::core::traits::sync::Async;

pub trait HasIbcEvents<Counterparty>: IbcChainContext<Counterparty>
where
    Counterparty: ChainContext,
{
    type WriteAcknowledgementEvent: Async;

    fn try_extract_write_acknowledgement_event(
        event: Self::Event,
    ) -> Option<Self::WriteAcknowledgementEvent>;
}
