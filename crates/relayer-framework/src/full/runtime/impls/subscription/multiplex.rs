use alloc::sync::Arc;
use core::marker::PhantomData;
use core::pin::Pin;
use futures::stream::Stream;

use crate::base::core::traits::sync::Async;
use crate::base::runtime::traits::mutex::HasMutex;
use crate::base::runtime::traits::subscription::{
    CanCreateSubscription, CanSubscribe, HasSubscriptionType,
};
use crate::full::runtime::traits::channel::{CanCreateChannels, CanUseChannels, HasChannelTypes};
use crate::std_prelude::*;

pub struct MultiplexingSubscriptionRuntime<Runtime>(pub PhantomData<Runtime>);

pub struct MultiplexingSubscription<Runtime, T>
where
    Runtime: HasChannelTypes + HasMutex,
{
    pub new_stream: Arc<
        dyn Fn() -> Option<Pin<Box<dyn Stream<Item = Arc<T>> + Send + 'static>>>
            + Send
            + Sync
            + 'static,
    >,
    pub phantom: PhantomData<Runtime>,
}
