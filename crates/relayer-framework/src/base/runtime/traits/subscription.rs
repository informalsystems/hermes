use async_trait::async_trait;
use core::future::Future;
use core::pin::Pin;
use futures::stream::Stream;

use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

#[async_trait]
pub trait Subscription: Send + Sync + 'static {
    type Item: Async;

    async fn subscribe(&self) -> Option<Pin<Box<dyn Stream<Item = Self::Item> + Send + 'static>>>;
}

pub fn closure_subscription<T: Async>(
    subscribe: impl Fn() -> Pin<
            Box<
                dyn Future<Output = Option<Pin<Box<dyn Stream<Item = T> + Send + 'static>>>>
                    + Send
                    + 'static,
            >,
        > + Send
        + Sync
        + 'static,
) -> impl Subscription<Item = T> {
    pub struct SubscriptionClosure<T> {
        pub subscribe: Box<
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
    impl<T: Async> Subscription for SubscriptionClosure<T> {
        type Item = T;

        async fn subscribe(
            &self,
        ) -> Option<Pin<Box<dyn Stream<Item = Self::Item> + Send + 'static>>> {
            (self.subscribe)().await
        }
    }

    SubscriptionClosure {
        subscribe: Box::new(subscribe),
    }
}
