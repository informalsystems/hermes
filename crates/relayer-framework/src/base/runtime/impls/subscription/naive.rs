use alloc::sync::Arc;
use async_trait::async_trait;
use core::pin::Pin;
use futures::stream::Stream;

use crate::base::core::traits::sync::Async;
use crate::base::runtime::traits::subscription::{
    CanCreateSubscription, CanSubscribe, HasSubscriptionType,
};
use crate::std_prelude::*;

pub struct NaiveSubscriptionRuntime;

pub struct NaiveSubscription<T> {
    pub new_stream: Arc<
        dyn Fn() -> Option<Pin<Box<dyn Stream<Item = Arc<T>> + Send + 'static>>>
            + Send
            + Sync
            + 'static,
    >,
}

impl<T> Clone for NaiveSubscription<T> {
    fn clone(&self) -> Self {
        Self {
            new_stream: self.new_stream.clone(),
        }
    }
}

impl HasSubscriptionType for NaiveSubscriptionRuntime {
    type Subscription<T: Async> = NaiveSubscription<T>;
}

#[async_trait]
impl CanSubscribe for NaiveSubscriptionRuntime {
    async fn subscribe<T>(
        subscription: &Self::Subscription<T>,
    ) -> Option<Pin<Box<dyn Stream<Item = Arc<T>> + Send + 'static>>>
    where
        T: Async,
    {
        (subscription.new_stream)()
    }
}

impl CanCreateSubscription for NaiveSubscriptionRuntime {
    fn new_subscription<T>(
        &self,
        new_stream: impl Fn() -> Option<Pin<Box<dyn Stream<Item = Arc<T>> + Send + 'static>>>
            + Send
            + Sync
            + 'static,
    ) -> Self::Subscription<T>
    where
        T: Async,
    {
        NaiveSubscription {
            new_stream: Arc::new(new_stream),
        }
    }
}
