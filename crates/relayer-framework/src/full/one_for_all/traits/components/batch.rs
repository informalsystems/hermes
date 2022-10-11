use crate::base::one_for_all::traits::relay::{OfaRelay, OfaRelayWrapper};
use crate::base::relay::traits::ibc_message_sender::IbcMessageSender;
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::full::batch::message_sender::HasIbcMessageSenderForBatchWorker;

pub trait OfaBatchComponents<Relay>
where
    Relay: OfaRelay,
{
    type IbcMessageSenderForBatchWorker: IbcMessageSender<OfaRelayWrapper<Relay>, SourceTarget>
        + IbcMessageSender<OfaRelayWrapper<Relay>, DestinationTarget>;
}

impl<Relay, Components> HasIbcMessageSenderForBatchWorker<SourceTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay<Components = Components>,
    Components: OfaBatchComponents<Relay>,
{
    type IbcMessageSenderForBatchWorker = Components::IbcMessageSenderForBatchWorker;
}

impl<Relay, Components> HasIbcMessageSenderForBatchWorker<DestinationTarget>
    for OfaRelayWrapper<Relay>
where
    Relay: OfaRelay<Components = Components>,
    Components: OfaBatchComponents<Relay>,
{
    type IbcMessageSenderForBatchWorker = Components::IbcMessageSenderForBatchWorker;
}
