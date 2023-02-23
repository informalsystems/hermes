use alloc::sync::Arc;
use core::future::Future;
use core::pin::Pin;

use async_trait::async_trait;
use futures::stream::Stream;

use crate::core::traits::sync::Async;
use crate::runtime::traits::mutex::HasMutex;
use crate::runtime::traits::subscription::Subscription;
use crate::std_prelude::*;

/**
   An auto trait that is implemented by all runtime contexts that implement
   [`HasMutex`]. This allows simple creation of [`Subscription`] values by
   wrapping an async closure that returns the same thing as
   [`subscribe`](Subscription::subscribe).

   The returned [`Subscription`] also implements guard to skip calling the
   underlying closure once the closure returns `None`.
*/
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
        let mut terminated = Runtime::acquire_mutex(&self.terminated).await;

        if *terminated {
            // If a subscription is terminated, it always return `None` from
            // that point onward.
            None
        } else {
            let m_stream = (self.subscribe)().await;

            if m_stream.is_none() {
                *terminated = true;
            }

            m_stream
        }
    }
}
