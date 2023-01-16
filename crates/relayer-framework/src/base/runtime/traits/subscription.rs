use core::pin::Pin;
use futures::stream::Stream;

use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

pub trait HasSubscriptionType {
    type Subscription<T: Async>: Async;
}

pub trait CanSubscribe: HasSubscriptionType {
    fn subscribe<'a, T>(
        subscription: &'a Self::Subscription<T>,
    ) -> Option<Pin<Box<dyn Stream<Item = T> + Send + 'static>>>
    where
        T: Async;
}

pub trait CanCreateSubscription: HasSubscriptionType {
    fn new_subscription<T>(
        stream: impl Fn() -> Option<Pin<Box<dyn Stream<Item = T> + Send + 'static>>>,
    ) -> Self::Subscription<T>
    where
        T: Async;
}
