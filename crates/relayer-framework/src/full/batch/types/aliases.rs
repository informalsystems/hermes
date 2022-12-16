use crate::base::chain::traits::types::{HasEventType, HasMessageType};
use crate::base::runtime::traits::runtime::HasRuntime;
use crate::full::runtime::traits::channel::HasChannelTypes;
use crate::full::runtime::traits::channel_once::HasChannelOnceTypes;
use crate::std_prelude::*;

pub type Sender<Chain, Payload> =
    <<Chain as HasRuntime>::Runtime as HasChannelTypes>::Sender<Payload>;

pub type Receiver<Chain, Payload> =
    <<Chain as HasRuntime>::Runtime as HasChannelTypes>::Receiver<Payload>;

pub type SenderOnce<Chain, Payload> =
    <<Chain as HasRuntime>::Runtime as HasChannelOnceTypes>::SenderOnce<Payload>;

pub type ReceiverOnce<Chain, Payload> =
    <<Chain as HasRuntime>::Runtime as HasChannelOnceTypes>::ReceiverOnce<Payload>;

pub type EventResult<Chain, Error> = Result<Vec<Vec<<Chain as HasEventType>::Event>>, Error>;

pub type EventResultSender<Chain, Error> = SenderOnce<Chain, EventResult<Chain, Error>>;

pub type EventResultReceiver<Chain, Error> = ReceiverOnce<Chain, EventResult<Chain, Error>>;

pub type BatchSubmission<Chain, Error> = (
    Vec<<Chain as HasMessageType>::Message>,
    EventResultSender<Chain, Error>,
);

pub type MessageBatchSender<Chain, Error> = Sender<Chain, BatchSubmission<Chain, Error>>;

pub type MessageBatchReceiver<Chain, Error> = Receiver<Chain, BatchSubmission<Chain, Error>>;
