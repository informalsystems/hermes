use crate::one_for_all::traits::chain::OfaChainTypes;
use crate::one_for_all::traits::runtime::OfaRuntime;
use crate::std_prelude::*;

pub type Runtime<Chain> = <Chain as OfaChainTypes>::Runtime;

pub type Mutex<Chain, Item> = <Runtime<Chain> as OfaRuntime>::Mutex<Item>;

pub type Sender<Chain, Payload> = <Runtime<Chain> as OfaRuntime>::Sender<Payload>;

pub type Receiver<Chain, Payload> = <Runtime<Chain> as OfaRuntime>::Receiver<Payload>;

pub type SenderOnce<Chain, Payload> = <Runtime<Chain> as OfaRuntime>::SenderOnce<Payload>;

pub type ReceiverOnce<Chain, Payload> = <Runtime<Chain> as OfaRuntime>::ReceiverOnce<Payload>;

pub type EventResult<Chain, Error> = Result<Vec<Vec<<Chain as OfaChainTypes>::Event>>, Error>;

pub type EventResultSender<Chain, Error> = SenderOnce<Chain, EventResult<Chain, Error>>;

pub type EventResultReceiver<Chain, Error> = ReceiverOnce<Chain, EventResult<Chain, Error>>;

pub type BatchSubmission<Chain, Error> = (
    Vec<<Chain as OfaChainTypes>::Message>,
    EventResultSender<Chain, Error>,
);

pub type MessageBatchSender<Chain, Error> = Sender<Chain, BatchSubmission<Chain, Error>>;

pub type MessageBatchReceiver<Chain, Error> = Receiver<Chain, BatchSubmission<Chain, Error>>;
