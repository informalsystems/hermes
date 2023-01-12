use async_trait::async_trait;
use core::pin::Pin;
use futures::stream::Stream;

use crate::base::chain::traits::types::event::HasEventType;
use crate::base::chain::traits::types::height::HasHeightType;
use crate::std_prelude::*;

/**
   A chain context implementing `CanCreateEventStream` allows the creation of a
   finite event stream that corresponds to the events emitted from a chain.

   The event stream is created as a [`Stream`] that emits a
   ([`Height`](HasHeightType::Height), [`Event`](HasEventType::Event)) tuple,
   to indicate that an event is emitted at the given chain height.

   The event height is expected to be incremental, i.e. the next event should
   have a height that is equal or greater than the height of a previous event.

   An event stream may be finite, in the sense that the stream may terminate.
   This can be caused by underlying errors such as network disconnection.
   In addition, an event stream cannot be shared with multiple consumers.

   Instead of trying to recover failure from the underlying source, we instead
   opt for failure recovery on the consumer side. i.e. if a consumer expects
   the event stream to be infinite, then in case when the stream is exhausted,
   the consumer would be the one that is responsible to retrieve a new event
   stream from an underlying source.

   We also leave the responsibility to share the event stream among multiple
   consumers to runtime constructs such as
   [`HasSubscriptionType`](crate::base::runtime::traits::subscription::HasSubscriptionType).
   The runtime-provided
   [`Subscription`](crate::base::runtime::traits::subscription::HasSubscriptionType::Subscription)
   type can multiplex a given event stream into multiple event streams to be
   used by multiple relay contexts.

   This means that the implementer for
   [`new_event_stream`](Self::new_event_stream) does not need to concern about
   managing the sharing of the event stream with multiple consumers, or
   recover from failure for the event stream. Instead, these concerns are
   handled at a higher layer by the relayer framework.
*/
#[async_trait]
pub trait CanCreateEventStream: HasHeightType + HasEventType {
    /**
       Create a new finite event stream.
    */
    async fn new_event_stream(&self) -> Pin<Box<dyn Stream<Item = (Self::Height, Self::Event)>>>;
}
