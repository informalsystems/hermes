use async_trait::async_trait;

use crate::base::chain::traits::types::{HasEventType, HasMessageType};
use crate::base::core::traits::error::HasErrorType;
use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

#[async_trait]
pub trait HasBatchChannelTypes: HasErrorType + HasEventType + HasMessageType {
    type SendMessageError: Async;

    type BatchSender: Async;
    type BatchReceiver: Async;

    type ResultSender: Async;
    type ResultReceiver: Async;

    fn new_batch_channel() -> (Self::BatchSender, Self::BatchReceiver);

    fn new_result_channel() -> (Self::ResultSender, Self::ResultReceiver);

    fn send_batch(
        sender: &Self::BatchSender,
        messages: Vec<Self::Message>,
        result_sender: Self::ResultSender,
    ) -> Result<(), Self::Error>;

    async fn try_receive_batch(
        receiver: &Self::BatchReceiver,
    ) -> Result<Option<(Vec<Self::Message>, Self::ResultSender)>, Self::Error>;

    async fn receive_result(
        result_receiver: Self::ResultReceiver,
    ) -> Result<Result<Vec<Vec<Self::Event>>, Self::SendMessageError>, Self::Error>;

    fn send_result(
        result_sender: Self::ResultSender,
        events: Result<Vec<Vec<Self::Event>>, Self::SendMessageError>,
    ) -> Result<(), Self::Error>;
}
