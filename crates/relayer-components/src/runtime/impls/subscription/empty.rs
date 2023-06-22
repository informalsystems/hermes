use core::marker::PhantomData;
use core::pin::Pin;

use async_trait::async_trait;
use futures_core::stream::Stream;

use crate::core::traits::sync::Async;
use crate::runtime::traits::subscription::Subscription;
use crate::std_prelude::*;

pub struct EmptySubscription<T>(pub PhantomData<T>);

impl<T> EmptySubscription<T> {
    pub fn new() -> Self {
        Self(PhantomData)
    }
}

#[async_trait]
impl<T: Async> Subscription for EmptySubscription<T> {
    type Item = T;

    async fn subscribe(&self) -> Option<Pin<Box<dyn Stream<Item = Self::Item> + Send + 'static>>> {
        None
    }
}
