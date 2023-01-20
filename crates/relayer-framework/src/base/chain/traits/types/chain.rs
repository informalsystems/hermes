use crate::base::core::traits::error::HasErrorType;
use crate::base::core::traits::sync::Async;
use crate::std_prelude::*;

use crate::base::chain::traits::types::event::HasEventType;
use crate::base::chain::traits::types::height::HasHeightType;
use crate::base::chain::traits::types::message::HasMessageType;

/**
   This covers the minimal abstract types that are used inside a chain context.

   A chain context have the following abstract types:

   -   [`Error`](HasErrorType::Error) - the error type encapsulating errors occured
       during chain operations.

   -   [`Height`](HasHeightType::Height) - the height of a chain, which should
        behave like natural numbers.

   -   [`Timestamp`](Self::Timestamp) - the timestamp of a chain, which should
       increment monotonically.

   -   [`Message`](HasMessageType::Message) - the messages being submitted
       to a chain.

   -   [`Event`](HasEventType::Event) - the events that are emitted after
       a transaction is committed to a chain.

    This trait only covers chain types that involve a single chain. For IBC
    chain types that involve _two_ chains, the abstract types are defined
    in [`HasIbcChainTypes`](super::ibc::HasIbcChainTypes).

    Notice that a chain context do not contain a `Transaction` abstract
    type. This is because we separate the concerns of normal chain operations
    from the special concerns of assembling chain messages into transactions
    and broadcasting it to the blockchain. See the
    [`transaction`](crate::base::transaction) module for more information
    about the transaction context.
*/
pub trait HasChainTypes: HasHeightType + HasMessageType + HasEventType + HasErrorType {
    type ChainId: Eq + Async;

    /**
       The timestamp of a chain, which should increment monotonically.

       By default, the timestamp only contains the `Ord` constraint, and does
       not support operations like adding to a `Duration`.

       We can impose additional constraints at the use site of `HasChainTypes`.
       However doing so may impose limitations on which concrete types
       the `Timestamp` type can be.

       By keeping the abstract type minimal, we can for example use
       simple `u8` or `u128` in seconds as the `Timestamp` type during testing,
       and use the more complex types like `DateTime` type during production.

       This especially helps given that having a canonical time type is
       still largely an unsolved problem in software engineering. Depending
       on the specific use cases, different concrete contexts may want to
       use different date time types to enforce certain invariants.
       By keeping this type abstract, we provide the flexibility to
       concrete context implementers to decide which exact time type
       they would like to use.
    */
    type Timestamp: Ord + Async;
}
