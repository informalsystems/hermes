use core::future::Future;
use core::pin::Pin;

use futures_util::stream::{self, StreamExt};
use ibc_relayer_components::core::traits::sync::Async;

use crate::std_prelude::*;

pub trait HasSpawner: Async {
    type Spawner: Spawner;

    fn spawner(&self) -> Self::Spawner;
}

pub trait Spawner: Async {
    fn spawn<F>(&self, task: F) -> Box<dyn TaskHandle>
    where
        F: Future + Send + 'static,
        F::Output: Send + 'static;
}

pub trait TaskHandle: Send + 'static {
    fn abort(self: Box<Self>);

    fn into_future(self: Box<Self>) -> Pin<Box<dyn Future<Output = ()> + Send + 'static>>;
}

impl TaskHandle for Vec<Box<dyn TaskHandle>> {
    fn abort(self: Box<Self>) {
        for handle in self.into_iter() {
            handle.abort();
        }
    }

    fn into_future(self: Box<Self>) -> Pin<Box<dyn Future<Output = ()> + Send + 'static>> {
        Box::pin(async move {
            stream::iter(self.into_iter())
                .for_each_concurrent(None, |handle| handle.into_future())
                .await;
        })
    }
}
