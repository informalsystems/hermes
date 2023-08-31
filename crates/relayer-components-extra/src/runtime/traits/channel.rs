/*!
   Support for use of abstract communication channels within a runtime context.

   This module define the abstract traits that can be implemented by a runtime
   context to support message-passing concurrency. This provides similar
   functionalities as the Rust channel types defined in
   [`std::sync::mpsc::channel`](https://doc.rust-lang.org/std/sync/mpsc/fn.channel.html).
*/

use core::pin::Pin;

use async_trait::async_trait;
use futures_core::stream::Stream;
use ibc_relayer_components::core::traits::error::HasErrorType;
use ibc_relayer_components::core::traits::sync::Async;

use crate::std_prelude::*;

/**
   Provides the abstract `Sender` and `Receiver` types for messsage-passing.

   The `Sender` and `Receiver` types are parameterized by an arbitrary payload
   type `T` using generic associated types. Given any payload type `T` that
   implements [`Async`], a runtime context that implements `HasChannelTypes`
   should be able to provide the concrete types `Sender<T>` and `Receiver<T>`,
   where messages of type `T` can be sent over to the `Sender<T>` end and
   received from the `Receiver<T>` end.

   The abstract `Sender` and `Receiver` types need to support the
   message-passing passing asynchronously, i.e. inside async functions.
   As a result, although it work similar to the Rust channel provided in
   the standard library,
   [`std::sync::mpsc::channel`](https://doc.rust-lang.org/std/sync/mpsc/fn.channel.html),
   the standard Rust channels are not suited for use here, as they could block
   the entire thread running the async tasks.

   Instead, there are async equivalent of the channel types offered by async
   libraries such as Tokio's
   [tokio::sync::mpsc::channel](https://docs.rs/tokio/latest/tokio/sync/mpsc/fn.channel.html)
   or async-std's [async_std::channel](https://docs.rs/async-std/latest/async_std/channel/index.html).

   A main difference between the channel types defined here and the common
   MPSC (multiple producer, single consumer) channels in the stated libraries
   is that we allow multiple consumers to use the same receiver. This is to
   avoid the use of `&mut` references, which would require the entire context
   containing a receiver to be mutable. Instead, concrete types can wrap a
   single-consumer receiver as `Arc<Mutex<Receiver<T>>>` in the concrete
   type definition, so that it can be used as a multi-consumer receiver.

   The methods for using the abstract channel types are available in separate
   traits, [`CanCreateChannels`] and [`CanUseChannels`]. This is because code
   that needs to create new channels do not necessary need to use the channels,
   and vice versa. Having separate traits makes it clear which capability a
   component needs from the runtime.

   There is also a similar trait
   [`HasChannelOnceTypes`](super::channel_once::HasChannelOnceTypes),
   which defines abstract one-shot channel types that allow at most one message
   to be sent over.
*/
pub trait HasChannelTypes: HasErrorType {
    /**
       The sender end of a channel with payload type `T`.
    */
    type Sender<T>: Async
    where
        T: Async;

    /**
       The receiver end of a channel with payload type `T`.
    */
    type Receiver<T>: Async
    where
        T: Async;
}

/**
   Allow the creation of new sender-receiver pairs for the channel types
   defined in [`HasChannelTypes`].
*/
pub trait CanCreateChannels: HasChannelTypes {
    /**
       Given a generic payload type `T`, create a
       [`Sender<T>`](HasChannelTypes::Sender<T>) and
       [`Receiver<T>`](HasChannelTypes::Receiver<T>) pair that are connected.

       The returned sender-receiver pair is expected to satisfy the following
       invariants:

         - Messages sent from the returned sender are expected to be received
           via the returned receiver.

         - Messages sent from mismatch sender should never be received by the
           given receiver.

       More invariants may be added in the future to better specify the
       requirements of the abstract channel. For now, we assume that mainstream
       implementation of Rust channels can all satisfy the same requirements.
    */
    fn new_channel<T>() -> (Self::Sender<T>, Self::Receiver<T>)
    where
        T: Async;
}

/**
   Allow the sending and receiving of message payloads over the
   [`Sender`](HasChannelTypes::Sender<T>) and
   [`Receiver`](HasChannelTypes::Receiver<T>) ends of a channel.
*/
#[async_trait]
pub trait CanUseChannels: HasChannelTypes {
    /**
       Given a reference to [`Sender<T>`](HasChannelTypes::Sender<T>),
       send a message payload of type `T` over the sender.

       If the receiver side of the channel has been dropped, the sending would
       fail and an error will be returned.

       The sending operation is _synchronous_. This ensures the payload is
       guaranteed to be in the channel queue after `send()` is called.

       The receiving operation is expected to be _asynchronous_. This means
       that any operation after `receive()` is called on the receiving end
       should _never_ execute within `send()`.
    */
    fn send<T>(sender: &Self::Sender<T>, value: T) -> Result<(), Self::Error>
    where
        T: Async;

    /**
       Given a reference to [`Receiver<T>`](HasChannelTypes::Receiver<T>),
       asynchronously receive a message payload of type `T` that is sent
       over the sender end.

       If the sender end is dropped before any value is sent, this would result
       in an error in `receive()`
    */
    async fn receive<T>(receiver: &mut Self::Receiver<T>) -> Result<T, Self::Error>
    where
        T: Async;

    fn try_receive<T>(receiver: &mut Self::Receiver<T>) -> Result<Option<T>, Self::Error>
    where
        T: Async;
}

pub trait CanStreamReceiver: HasChannelTypes {
    fn receiver_to_stream<T>(
        receiver: Self::Receiver<T>,
    ) -> Pin<Box<dyn Stream<Item = T> + Send + 'static>>
    where
        T: Async;
}

pub trait CanCloneSender: HasChannelTypes {
    fn clone_sender<T>(sender: &Self::Sender<T>) -> Self::Sender<T>
    where
        T: Async;
}
