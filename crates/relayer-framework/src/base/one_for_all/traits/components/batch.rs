use crate::base::one_for_all::traits::relay::{OfaRelay, OfaRelayContext};
use crate::base::traits::ibc_message_sender::IbcMessageSender;
use crate::base::traits::target::{DestinationTarget, SourceTarget};
use crate::full::batch::message_sender::HasIbcMessageSenderForBatchWorker;

pub trait OfaBatchComponents<Relay>
where
    Relay: OfaRelay,
{
    type IbcMessageSenderForBatchWorker: IbcMessageSender<OfaRelayContext<Relay>, SourceTarget>
        + IbcMessageSender<OfaRelayContext<Relay>, DestinationTarget>;
}

impl<Relay, Components> HasIbcMessageSenderForBatchWorker<SourceTarget> for OfaRelayContext<Relay>
where
    Relay: OfaRelay<Components = Components>,
    Components: OfaBatchComponents<Relay>,
{
    type IbcMessageSenderForBatchWorker = Components::IbcMessageSenderForBatchWorker;
}

impl<Relay, Components> HasIbcMessageSenderForBatchWorker<DestinationTarget>
    for OfaRelayContext<Relay>
where
    Relay: OfaRelay<Components = Components>,
    Components: OfaBatchComponents<Relay>,
{
    type IbcMessageSenderForBatchWorker = Components::IbcMessageSenderForBatchWorker;
}
