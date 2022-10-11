use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::one_for_all::types::relay::OfaRelayWrapper;
use crate::base::relay::traits::ibc_message_sender::IbcMessageSender;
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::full::batch::message_sender::HasIbcMessageSenderForBatchWorker;

pub trait OfaBatchComponents<Relay>
where
    Relay: OfaBaseRelay,
{
    type IbcMessageSenderForBatchWorker: IbcMessageSender<OfaRelayWrapper<Relay>, SourceTarget>
        + IbcMessageSender<OfaRelayWrapper<Relay>, DestinationTarget>;
}

impl<Relay, Components> HasIbcMessageSenderForBatchWorker<SourceTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay<Components = Components>,
    Components: OfaBatchComponents<Relay>,
{
    type IbcMessageSenderForBatchWorker = Components::IbcMessageSenderForBatchWorker;
}

impl<Relay, Components> HasIbcMessageSenderForBatchWorker<DestinationTarget>
    for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay<Components = Components>,
    Components: OfaBatchComponents<Relay>,
{
    type IbcMessageSenderForBatchWorker = Components::IbcMessageSenderForBatchWorker;
}
