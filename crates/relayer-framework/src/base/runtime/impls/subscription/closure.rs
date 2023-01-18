use alloc::sync::Arc;
use async_trait::async_trait;
use core::future::Future;
use core::pin::Pin;
use futures::stream::Stream;

use crate::base::core::traits::sync::Async;
use crate::base::runtime::traits::mutex::HasMutex;
use crate::base::runtime::traits::subscription::Subscription;
use crate::std_prelude::*;

pub trait CanCreateClosureSubscription {
    fn new_closure_subscription<T: Async>(
        subscribe: impl Fn() -> Pin<
                Box<
                    dyn Future<Output = Option<Pin<Box<dyn Stream<Item = T> + Send + 'static>>>>
                        + Send
                        + 'static,
                >,
            > + Send
            + Sync
            + 'static,
    ) -> Arc<dyn Subscription<Item = T>>;
}

impl<Runtime> CanCreateClosureSubscription for Runtime
where
    Runtime: HasMutex,
{
    fn new_closure_subscription<T: Async>(
        subscribe: impl Fn() -> Pin<
                Box<
                    dyn Future<Output = Option<Pin<Box<dyn Stream<Item = T> + Send + 'static>>>>
                        + Send
                        + 'static,
                >,
            > + Send
            + Sync
            + 'static,
    ) -> Arc<dyn Subscription<Item = T>> {
        let subscription: SubscriptionClosure<Runtime, T> = SubscriptionClosure {
            terminated: Runtime::new_mutex(false),
            subscribe: Box::new(subscribe),
        };

        Arc::new(subscription)
    }
}

struct SubscriptionClosure<Runtime, T>
where
    Runtime: HasMutex,
{
    terminated: <Runtime as HasMutex>::Mutex<bool>,
    subscribe: Box<
        dyn Fn() -> Pin<
                Box<
                    dyn Future<Output = Option<Pin<Box<dyn Stream<Item = T> + Send + 'static>>>>
                        + Send
                        + 'static,
                >,
            > + Send
            + Sync
            + 'static,
    >,
}

#[async_trait]
impl<Runtime, T: Async> Subscription for SubscriptionClosure<Runtime, T>
where
    Runtime: HasMutex,
{
    type Item = T;

    async fn subscribe(&self) -> Option<Pin<Box<dyn Stream<Item = Self::Item> + Send + 'static>>> {
        if *Runtime::acquire_mutex(&self.terminated).await {
            None
        } else {
            let m_stream = (self.subscribe)().await;

            if m_stream.is_none() {
                *Runtime::acquire_mutex(&self.terminated).await = true;
            }

            m_stream
        }
    }
}
