use alloc::sync::Arc;
use async_trait::async_trait;
use core::future::Future;
use core::pin::Pin;
use futures::stream::Stream;

use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

/**
    A [`Subscription`] is a multi-consumer abstraction over a single-consumer
    [`Stream`] construct. A [`Subscription`] value can be shared by wrapping
    it inside an `Arc<dyn Subscription>`. Each call to the
    [`subscribe`](Self::subscribe) method would optionally return a [`Stream`]
    that can be used by a single consumer.

    The expected behavior of a [`Subscription`] implementation is that the
    [`Stream`]s returned from multiple calls to [`subscribe`](Self::subscribe)
    should yield the same stream of items, modulo the race conditions between
    each calls and errors from underlying sources.

    A naive implementation of [`Subscription`] would subscribe from multiple
    underlying sources, such as a network connection, each time
    [`subscribe`](Self::subscribe) is called. This may be inefficient as each
    stream would have to open new network connections, but it is simpler and
    more resilient to error conditions such as network disconnections. A simple
    way to implement a naive subscription is to use [`closure_subscription`]
    to turn a closure into a [`Subscription`].

    A [`Subscription`] implementation could be made efficient by sharing one
    incoming [`Stream`] with multiple consumers, by multiplexing them to multiple
    outgoing [`Stream`]s inside a background task. An example implementation of
    this is the
    [`multiplex_subscription`](crate::full::runtime::impls::subscription::multiplex::multiplex_subscription)
    function, which wraps around a naive [`Subscription`] and perform
    multiplexing and recovery from a background task.

    A [`Subscription`] do not guarantee whether the returned [`Stream`] is
    finite or infinite (long-running). As a result, the [`Stream`] returned
    from [`subscribe`](Self::subscribe) may terminate, in case if there is
    underlying source encounter errors such as network disconnection. However,
    a long-running consumer may call [`subscribe`](Self::subscribe) again in
    attempt to obtain a new [`Stream`].

    A [`Subscription`] can be terminated by an underlying controller, such as
    during program shutdown. When a subscription is terminated, it is expected
    to return `None` for all subsequent calls to [`subscribe`](Self::subscribe).
    A long-running consumer can treat the returned `None` as a signal that
    the subscription is terminated, and in turns terminate itself. The
    underlying controller is also expected to terminate all currently running
    [`Stream`]s, so that the running consumers would receive the termination
    signal.
*/
#[async_trait]
pub trait Subscription: Send + Sync + 'static {
    /**
       The item that is yielded in the [`Stream`]s returned from
       [`subscribe`](Self::subscribe).
    */
    type Item: Async;

    /**
       If the subscription is still active, returns a new single consumer
       [`Stream`] which would produce a stream of items that are produced
       _after_ the method is called.

       The items produced prior to the call to [`subscribe`](Self::subscribe)
       are lost. This is to allow the underlying subscription implementation
       to preserve memory and not store all items that are produced since the
       subscription is created.

       If the subscription is terminated, the method would return `None`.
       Callers that receive `None` should expect all subsequent calls to
       [`subscribe`](Self::subscribe) to also return `None`, and perform
       appropriate actions for termination.
    */
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

#[async_trait]
impl<T: Async> Subscription for Box<dyn Subscription<Item = T>> {
    type Item = T;

    async fn subscribe(&self) -> Option<Pin<Box<dyn Stream<Item = Self::Item> + Send + 'static>>> {
        self.as_ref().subscribe().await
    }
}

#[async_trait]
impl<T: Async> Subscription for Arc<dyn Subscription<Item = T>> {
    type Item = T;

    async fn subscribe(&self) -> Option<Pin<Box<dyn Stream<Item = Self::Item> + Send + 'static>>> {
        self.as_ref().subscribe().await
    }
}
