use alloc::sync::Arc;
use core::ops::DerefMut;
use futures::stream::{Stream, StreamExt};

use crate::base::core::traits::sync::Async;
use crate::base::runtime::traits::mutex::HasMutex;
use crate::base::runtime::traits::subscription::Subscription;
use crate::full::runtime::impls::subscription::multiplex::MultiplexingSubscription;
use crate::full::runtime::traits::channel::{CanCreateChannels, CanStreamReceiver, CanUseChannels};
use crate::full::runtime::traits::spawn::{HasSpawner, Spawner};
use crate::std_prelude::*;

/**
   Allows multiplexing of a single [`Stream`] into a subscription.
   This is an auto trait implemented by all runtime contexts that implement
   [`HasSpawner`], [`HasMutex`], [`CanCreateChannels`], [`CanUseChannels`],
   and [`CanStreamReceiver`].

   When the stream terminates, the subscription also terminates.
*/
pub trait CanStreamSubscription {
    fn stream_subscription<T>(
        &self,
        stream: impl Stream<Item = T> + Send + 'static,
    ) -> Arc<dyn Subscription<Item = T>>
    where
        T: Async + Clone;
}

impl<Runtime> CanStreamSubscription for Runtime
where
    Runtime: HasSpawner + HasMutex + CanCreateChannels + CanUseChannels + CanStreamReceiver,
{
    fn stream_subscription<T>(
        &self,
        stream: impl Stream<Item = T> + Send + 'static,
    ) -> Arc<dyn Subscription<Item = T>>
    where
        T: Async + Clone,
    {
        let stream_senders = Arc::new(Runtime::new_mutex(Some(Vec::new())));

        let spawner = self.spawner();
        let task_senders = stream_senders.clone();

        spawner.spawn(async move {
            let task_senders = &task_senders;

            stream
                .for_each(|item| async move {
                    let mut m_senders = Runtime::acquire_mutex(task_senders).await;

                    if let Some(senders) = m_senders.deref_mut() {
                        // Remove senders where the receiver side has been dropped
                        senders.retain(|sender| Runtime::send(sender, item.clone()).is_ok());
                    }
                })
                .await;

            let mut senders = Runtime::acquire_mutex(task_senders).await;
            *senders = None;
        });

        let subscription: MultiplexingSubscription<Runtime, T> =
            MultiplexingSubscription { stream_senders };

        Arc::new(subscription)
    }
}
