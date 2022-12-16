use crate::base::one_for_all::traits::chain::OfaChainTypes;
use crate::base::one_for_all::traits::runtime::OfaFullRuntime;
use crate::std_prelude::*;

pub type Sender<Chain, Payload> =
    <<Chain as OfaChainTypes>::Runtime as OfaFullRuntime>::Sender<Payload>;

pub type Receiver<Chain, Payload> =
    <<Chain as OfaChainTypes>::Runtime as OfaFullRuntime>::Receiver<Payload>;

pub type SenderOnce<Chain, Payload> =
    <<Chain as OfaChainTypes>::Runtime as OfaFullRuntime>::SenderOnce<Payload>;

pub type ReceiverOnce<Chain, Payload> =
    <<Chain as OfaChainTypes>::Runtime as OfaFullRuntime>::ReceiverOnce<Payload>;

pub type EventResult<Chain, Error> = Result<Vec<Vec<<Chain as OfaChainTypes>::Event>>, Error>;

pub type EventResultSender<Chain, Error> = SenderOnce<Chain, EventResult<Chain, Error>>;

pub type EventResultReceiver<Chain, Error> = ReceiverOnce<Chain, EventResult<Chain, Error>>;

pub type BatchSubmission<Chain, Error> = (
    Vec<<Chain as OfaChainTypes>::Message>,
    EventResultSender<Chain, Error>,
);

pub type MessageBatchSender<Chain, Error> = Sender<Chain, BatchSubmission<Chain, Error>>;

pub type MessageBatchReceiver<Chain, Error> = Receiver<Chain, BatchSubmission<Chain, Error>>;
