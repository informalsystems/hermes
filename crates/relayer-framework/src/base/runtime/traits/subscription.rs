use alloc::sync::Arc;
use core::pin::Pin;
use futures::stream::Stream;

use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

/**
   An abstraction provided by the runtime context to provide a shareable and
   recoverable pub-sub subscription.

   The [`Subscription`](Self::Subscription) generic associated type provides an
   abstract subscription type that can be used multiple times to obtain a
   single-consumer [`Stream`].

   The consumer interface for the subscription is available at [`CanSubscribe`],
   and the provider interface is available at [`CanCreateSubscription`].

   The underlying implementation of the subscription is expected to work by
   multiplexing one incoming [`Stream`] into multiple outgoing [`Stream`]s with
   the same item type. This requires a background task to be running to
   multiplex the incoming items into each outgoing streams.

   The subscription type also supports optional re-subscription by attempt to
   re-create the incoming [`Stream`]. This is to support use cases such as
   recovery from network disconnection. Note however that when an incoming
   [`Stream`] ends, all corresponding outgoing [`Stream`]s would end as well.
   Instead, the consumers are expected to resubscribe to the subscription to
   obtain new outgoing [`Stream`]s that correspond to the new incoming
   [`Stream`].
*/
pub trait HasSubscriptionType {
    /**
       A subscription with item type `T` that can be shared with multiple
       consumers through cloning.

       When called with [`CanSubcribe::subscribe`], this returns a finite
       [`Stream<Item = Arc<T>>`].
    */
    type Subscription<T: Async>: Clone + Async;
}

/**
   Provides the consumer interface of [`HasSubscriptionType`] for subscribing
   to a stream.
*/
pub trait CanSubscribe: HasSubscriptionType {
    /**
       Given a reference to a [`Subscription<T>`](HasSubscriptionType::Subscription),
       optionally returns a [`Stream<Item = Arc<T>`]. When `subscribe` returns
       [`None`], this indicates that the subcription has been ended from the
       upstream, and no more item is available.

       The returned stream produces a finite stream of `Arc<T>` that correspond
       to the items from underlying incoming stream starting from the rough
       time that `subscribe` is called. Note that the items that are produced
       by the underlying incoming stream _before_ `subscribe` is called are
       lost.

       The returned [`Stream`] is a finite stream that ends when the underlying
       incoming stream ended. If a consumer expects the incoming stream to be
       infinite, they can call `subscribe` again to get a new stream that
       correspond to a new incoming stream that replace the original stream.
    */
    fn subscribe<T>(
        subscription: &Self::Subscription<T>,
    ) -> Option<Pin<Box<dyn Stream<Item = Arc<T>> + Send + 'static>>>
    where
        T: Async;
}

/**
   Provides the provider interface of [`HasSubscriptionType`] for creating
   new subscriptions.
*/
pub trait CanCreateSubscription: HasSubscriptionType {
    /**
       Create a new [`Subscription<T>`](HasSubscriptionType::Subscription) by
       providing a `new_stream` closure that when called, return an optional
       [`Stream<Item = Arc<T>>`].

       The `new_stream` closure is expected to return brand new [`Stream`]s
       that are independent of the previous call. For example, if the given
       stream is created from a network source, then calling `new_stream`
       twice would result in two separate network connections.

       An efficient runtime subscription implementation would avoid calling
       `new_stream` multiple times. Instead, the same stream returned by
       `new_stream` would be reused across multiple outgoing streams by having
       a background task that performs the stream multiplexing.

       The `new_stream` closure may return `None` to indicate that the
       subscription is terminated through external processes, such as during
       shutdown. Once `None` is returned, the background task would terminate,
       and any new call to [`subscribe`](CanSubscribe::subscribe) would return
       `None`.

       Note that it is up to the implementer of the [`Stream`] returned from
       `new_stream` to stop it from returning new items. The subscription
       background task _may_ continue to run until the current incoming stream
       terminates, which it would in turn terminate when calling `new_stream`
       which returns `None`.

       It is also worth noting that a naive runtime subscription implementation
       _may_ call `new_stream` every time [`subscribe`](CanSubscribe::subscribe)
       is called, such as when implemented by a mock runtime or single-threaded
       runtime. It is implementation-dependent of when `new_stream` would be
       called.
    */
    fn new_subscription<T>(
        new_stream: impl Fn() -> Option<Pin<Box<dyn Stream<Item = Arc<T>> + Send + 'static>>>
            + Send
            + Sync
            + 'static,
    ) -> Self::Subscription<T>
    where
        T: Async;
}
