use alloc::sync::Arc;
use async_trait::async_trait;
use core::pin::Pin;
use futures::stream::{Stream, StreamExt};

use crate::base::core::traits::sync::Async;
use crate::base::runtime::traits::mutex::HasMutex;
use crate::base::runtime::traits::subscription::Subscription;
use crate::full::runtime::traits::channel::{
    CanCreateChannels, CanStreamReceiver, CanUseChannels, HasChannelTypes,
};
use crate::full::runtime::traits::spawn::{HasSpawner, Spawner};
use crate::std_prelude::*;

pub type StreamSender<Runtime, T> = <Runtime as HasChannelTypes>::Sender<T>;

pub type StreamSenders<Runtime, T> =
    Arc<<Runtime as HasMutex>::Mutex<Option<Vec<StreamSender<Runtime, T>>>>>;

pub struct MultiplexingSubscriptionRuntime<Runtime> {
    pub runtime: Runtime,
}

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

#[async_trait]
impl<Runtime, T> Subscription for MultiplexingSubscription<Runtime, T>
where
    T: Async,
    Runtime: HasMutex + CanCreateChannels + CanStreamReceiver,
{
    type Item = T;

    async fn subscribe(&self) -> Option<Pin<Box<dyn Stream<Item = T> + Send + 'static>>>
    where
        T: Async,
    {
        let mut m_senders = Runtime::acquire_mutex(&self.stream_senders).await;

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

pub async fn multiplex_subscription<Runtime, T>(
    runtime: &Runtime,
    in_subscription: Arc<dyn Subscription<Item = T>>,
) -> Arc<dyn Subscription<Item = T>>
where
    T: Async + Clone,
    Runtime: HasSpawner + HasMutex + CanCreateChannels + CanUseChannels + CanStreamReceiver,
{
    let stream_senders = Arc::new(Runtime::new_mutex(Some(Vec::new())));

    let spawner = runtime.spawner();
    let task_senders = stream_senders.clone();

    spawner.spawn(async move {
        loop {
            let m_stream = in_subscription.subscribe().await;

            {
                let mut senders = Runtime::acquire_mutex(&task_senders).await;
                *senders = Some(Vec::new());
            }

            match m_stream {
                Some(stream) => {
                    let task_senders = &task_senders;
                    stream
                        .for_each(|item| async move {
                            let item = item.clone();
                            let m_senders = Runtime::acquire_mutex(&task_senders).await;
                            if let Some(senders) = m_senders.as_ref() {
                                for sender in senders.iter() {
                                    let _ = Runtime::send(sender, item.clone());
                                }
                            }
                        })
                        .await;
                }
                None => {
                    let mut senders = Runtime::acquire_mutex(&task_senders).await;
                    *senders = None;
                    return;
                }
            }
        }
    });

    let subscription: MultiplexingSubscription<Runtime, T> =
        MultiplexingSubscription { stream_senders };

    Arc::new(subscription)
}
