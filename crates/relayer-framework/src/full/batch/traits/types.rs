use async_trait::async_trait;

use crate::base::chain::traits::types::{HasEventType, HasMessageType};
use crate::base::core::traits::error::HasErrorType;
use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

#[async_trait]
pub trait HasBatchChannelTypes: HasErrorType + HasEventType + HasMessageType {
    type SendMessageError: Async;

    type MessageBatchSender: Async;
    type MessageBatchReceiver: Async;

    type EventResultSender: Async;
    type EventResultReceiver: Async;

    fn new_batch_channel() -> (Self::MessageBatchSender, Self::MessageBatchReceiver);

    fn new_result_channel() -> (Self::EventResultSender, Self::EventResultReceiver);

    fn send_batch(
        sender: &Self::MessageBatchSender,
        messages: Vec<Self::Message>,
        result_sender: Self::EventResultSender,
    ) -> Result<(), Self::Error>;

    async fn try_receive_batch(
        receiver: &Self::MessageBatchReceiver,
    ) -> Result<Option<(Vec<Self::Message>, Self::EventResultSender)>, Self::Error>;

    async fn receive_result(
        result_receiver: Self::EventResultReceiver,
    ) -> Result<Result<Vec<Vec<Self::Event>>, Self::SendMessageError>, Self::Error>;

    fn send_result(
        result_sender: Self::EventResultSender,
        events: Result<Vec<Vec<Self::Event>>, Self::SendMessageError>,
    ) -> Result<(), Self::Error>;
}
