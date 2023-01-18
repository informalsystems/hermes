use alloc::sync::Arc;
use async_trait::async_trait;
use core::ops::DerefMut;
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

/**
   Multiplex the incoming [`Stream`] provided by an underlying [`Subscription`]
   into multiple outgoing [`Stream`]s through a background task. This is
   an auto trait implemented by all runtime contexts that implement
   [`HasSpawner`], [`HasMutex`], [`CanCreateChannels`], [`CanUseChannels`],
   and [`CanStreamReceiver`].

   This can be used to improve the efficiency of naive subscriptions created from
   [`CanCreateClosureSubscription`](crate::base::runtime::impls::subscription::closure::CanCreateClosureSubscription).
   For example, one can first create a subscription closure that establishes
   new network connection each time `subscribe` is called. The subscription
   closure is then passed to [`multiplex_subscription`](Self::multiplex_subscription),
   which would return a wrapped subscription which would only create one
   network connection at a time.

   The multiplexed subscription also attempts to recover by calling the
   [`subscribe`](Subscription::subscribe) method of the underlying subsciption
   again, if a given [`Stream`] terminates. This would allow for auto recovery
   from underlying errors such as network disconnection. The multiplexed
   subscription would only terminate if the underlying
   [`subscribe`](Subscription::subscribe) returns `None`.

   The streams returned from the [`subscribe`](Subscription::subscribe) of
   the multiplexed subscription will automatically resume streaming from
   a new underlying stream, if the original underlying stream is terminated.
   However, since a consumer cannot know if a [`Subscription`] implementation
   is multiplexed or not, it should always retry calling
   [`subscribe`](Subscription::subscribe) in case a [`Stream`] ends.
*/
#[async_trait]
pub trait CanMultiplexSubscription {
    /**
       Multiplex a given subscription, with a mapper function that maps the
       item coming from the underlying subscription from `T` to `U`. Returns
       a new multiplexed subscription that shares the same underlying [`Stream`].
    */
    async fn multiplex_subscription<T, U>(
        &self,
        subscription: impl Subscription<Item = T>,
        map_item: impl Fn(T) -> U + Send + Sync + 'static,
    ) -> Arc<dyn Subscription<Item = U>>
    where
        T: Async + Clone,
        U: Async + Clone;
}

#[async_trait]
impl<Runtime> CanMultiplexSubscription for Runtime
where
    Runtime: HasSpawner + HasMutex + CanCreateChannels + CanUseChannels + CanStreamReceiver,
{
    async fn multiplex_subscription<T, U>(
        &self,
        in_subscription: impl Subscription<Item = T>,
        map_item: impl Fn(T) -> U + Send + Sync + 'static,
    ) -> Arc<dyn Subscription<Item = U>>
    where
        T: Async + Clone,
        U: Async + Clone,
    {
        let stream_senders = Arc::new(Runtime::new_mutex(Some(Vec::new())));

        let spawner = self.spawner();
        let task_senders = stream_senders.clone();

        spawner.spawn(async move {
            loop {
                let m_stream = in_subscription.subscribe().await;

                match m_stream {
                    Some(stream) => {
                        let task_senders = &task_senders;
                        let map_item = &map_item;

                        stream
                            .for_each(|item| async move {
                                let mapped = map_item(item);
                                let mut m_senders = Runtime::acquire_mutex(task_senders).await;

                                if let Some(senders) = m_senders.deref_mut() {
                                    // Remove senders where the receiver side has been dropped
                                    senders.retain(|sender| {
                                        Runtime::send(sender, mapped.clone()).is_ok()
                                    });
                                }
                            })
                            .await;
                    }
                    None => {
                        // If the underlying subscription returns `None` from `subscribe`, clears the senders
                        // queue inside the mutex and set it to `None` and return. This will cause subsequent
                        // calls to `subscribe` for the multiplexed subscription to also return `None`.
                        let mut senders = Runtime::acquire_mutex(&task_senders).await;
                        *senders = None;
                        return;
                    }
                }
            }
        });

        let subscription: MultiplexingSubscription<Runtime, U> =
            MultiplexingSubscription { stream_senders };

        Arc::new(subscription)
    }
}

type StreamSender<Runtime, T> = <Runtime as HasChannelTypes>::Sender<T>;

type StreamSenders<Runtime, T> =
    Arc<<Runtime as HasMutex>::Mutex<Option<Vec<StreamSender<Runtime, T>>>>>;

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
