use alloc::sync::Arc;
use async_trait::async_trait;
use core::marker::PhantomData;
use core::pin::Pin;
use futures::stream::Stream;

use crate::base::core::traits::sync::Async;
use crate::base::runtime::traits::mutex::HasMutex;
use crate::base::runtime::traits::subscription::{
    CanCreateSubscription, CanSubscribe, HasSubscriptionType,
};
use crate::full::runtime::traits::channel::{
    CanCreateChannels, CanStreamReceiver, CanUseChannels, HasChannelTypes,
};
use crate::std_prelude::*;

pub type StreamSender<Runtime, T> = <Runtime as HasChannelTypes>::Sender<Arc<T>>;

pub type StreamSenders<Runtime, T> =
    Arc<<Runtime as HasMutex>::Mutex<Option<Vec<StreamSender<Runtime, T>>>>>;

pub struct MultiplexingSubscriptionRuntime<Runtime>(pub PhantomData<Runtime>);

pub struct MultiplexingSubscription<Runtime, T>
where
    T: Async,
    Runtime: HasChannelTypes + HasMutex,
{
    pub stream_senders: StreamSenders<Runtime, T>,
}

impl<Runtime, T> Clone for MultiplexingSubscription<Runtime, T>
where
    T: Async,
    Runtime: HasChannelTypes + HasMutex,
{
    fn clone(&self) -> Self {
        Self {
            stream_senders: self.stream_senders.clone(),
        }
    }
}

impl<Runtime> HasSubscriptionType for MultiplexingSubscriptionRuntime<Runtime>
where
    Runtime: HasChannelTypes + HasMutex,
{
    type Subscription<T: Async> = MultiplexingSubscription<Runtime, T>;
}

#[async_trait]
impl<Runtime> CanSubscribe for MultiplexingSubscriptionRuntime<Runtime>
where
    Runtime: HasMutex + CanCreateChannels + CanStreamReceiver,
{
    async fn subscribe<T>(
        subscription: &Self::Subscription<T>,
    ) -> Option<Pin<Box<dyn Stream<Item = Arc<T>> + Send + 'static>>>
    where
        T: Async,
    {
        let mut m_senders = Runtime::acquire_mutex(&subscription.stream_senders).await;

        match m_senders.as_mut() {
            Some(senders) => {
                let (sender, receiver) = Runtime::new_channel();
                senders.push(sender);

                let stream = Runtime::receiver_to_stream(receiver);
                Some(stream)
            }
            None => None,
        }
    }
}
