use crate::base::chain::traits::types::{HasEventType, HasMessageType};
use crate::base::core::traits::error::HasErrorType;
use crate::base::relay::traits::target::ChainTarget;
use crate::base::runtime::traits::channel::HasChannelTypes;
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::std_prelude::*;

pub type TargetChain<Relay, Target> = <Target as ChainTarget<Relay>>::TargetChain;

pub type Sender<Relay, Target, Payload> =
    <<TargetChain<Relay, Target> as HasRuntime>::Runtime as HasChannelTypes>::Sender<Payload>;

pub type Receiver<Relay, Target, Payload> =
    <<TargetChain<Relay, Target> as HasRuntime>::Runtime as HasChannelTypes>::Receiver<Payload>;

pub type EventResult<Relay, Target> = (
    <TargetChain<Relay, Target> as HasEventType>::Event,
    <Relay as HasErrorType>::Error,
);

pub type BatchSubmission<Relay, Target> = (
    Vec<<TargetChain<Relay, Target> as HasMessageType>::Message>,
    EventResultSender<Relay, Target>,
);

pub type EventResultSender<Relay, Target> = Sender<Relay, Target, EventResult<Relay, Target>>;

pub type EventResultResult<Relay, Target> = Receiver<Relay, Target, EventResult<Relay, Target>>;

pub type MessageBatchSender<Relay, Target> = Sender<Relay, Target, BatchSubmission<Relay, Target>>;

pub type MessageBatchReceiver<Relay, Target> =
    Receiver<Relay, Target, BatchSubmission<Relay, Target>>;
