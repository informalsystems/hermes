use crate::base::one_for_all::traits::relay::OfaBaseRelay;
use crate::base::relay::traits::ibc_message_sender::IbcMessageSender;
use crate::base::relay::traits::target::{DestinationTarget, SourceTarget};
use crate::common::one_for_all::types::relay::OfaRelayWrapper;
use crate::full::batch::message_sender::HasIbcMessageSenderForBatchWorker;

pub trait OfaBatchPreset<Relay>
where
    Relay: OfaBaseRelay,
{
    type IbcMessageSenderForBatchWorker: IbcMessageSender<OfaRelayWrapper<Relay>, SourceTarget>
        + IbcMessageSender<OfaRelayWrapper<Relay>, DestinationTarget>;
}

impl<Relay, Preset> HasIbcMessageSenderForBatchWorker<SourceTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay<Preset = Preset>,
    Preset: OfaBatchPreset<Relay>,
{
    type IbcMessageSenderForBatchWorker = Preset::IbcMessageSenderForBatchWorker;
}

impl<Relay, Preset> HasIbcMessageSenderForBatchWorker<DestinationTarget> for OfaRelayWrapper<Relay>
where
    Relay: OfaBaseRelay<Preset = Preset>,
    Preset: OfaBatchPreset<Relay>,
{
    type IbcMessageSenderForBatchWorker = Preset::IbcMessageSenderForBatchWorker;
}
