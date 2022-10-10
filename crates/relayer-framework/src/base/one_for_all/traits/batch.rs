use async_trait::async_trait;
use core::marker::PhantomData;

use crate::base::one_for_all::traits::chain::OfaChainTypes;
use crate::base::traits::core::Async;
use crate::std_prelude::*;

#[derive(Clone)]
pub struct OfaBatchContext<Chain> {
    pub phantom: PhantomData<Chain>,
}

#[async_trait]
pub trait OfaBatch<Chain: OfaChainTypes>: Async {
    type BatchSender: Async;
    type BatchReceiver: Async;

    type ResultSender: Async;
    type ResultReceiver: Async;

    fn new_batch_channel() -> (Self::BatchSender, Self::BatchReceiver);

    fn new_result_channel() -> (Self::ResultSender, Self::ResultReceiver);

    async fn send_batch(
        sender: &Self::BatchSender,
        messages: Vec<Chain::Message>,
        result_sender: Self::ResultSender,
    ) -> Result<(), Chain::Error>;

    async fn try_receive_batch(
        receiver: &Self::BatchReceiver,
    ) -> Result<Option<(Vec<Chain::Message>, Self::ResultSender)>, Chain::Error>;

    async fn receive_result(
        result_receiver: Self::ResultReceiver,
    ) -> Result<Result<Vec<Vec<Chain::Event>>, Chain::Error>, Chain::Error>;

    fn send_result(
        result_sender: Self::ResultSender,
        events: Result<Vec<Vec<Chain::Event>>, Chain::Error>,
    ) -> Result<(), Chain::Error>;
}
