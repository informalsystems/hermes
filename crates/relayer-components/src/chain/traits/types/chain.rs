/*!
   Trait definition for [`HasChainTypes`].
*/

use crate::base::chain::traits::types::chain_id::HasChainIdType;
use crate::base::chain::traits::types::event::HasEventType;
use crate::base::chain::traits::types::height::HasHeightType;
use crate::base::chain::traits::types::message::HasMessageType;
use crate::base::chain::traits::types::timestamp::HasTimestampType;
use crate::base::core::traits::error::HasErrorType;

/**
   This covers the minimal abstract types that are used inside a chain context.

   A chain context have the following abstract types:

   -   [`Error`](HasErrorType::Error) - the error type encapsulating errors occured
       during chain operations.

   -   [`Height`](HasHeightType::Height) - the height of a chain, which should
        behave like natural numbers.

   -   [`Timestamp`](HasTimestampType::Timestamp) - the timestamp of a chain, which should
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
pub trait HasChainTypes:
    HasHeightType + HasMessageType + HasEventType + HasChainIdType + HasTimestampType + HasErrorType
{
}

impl<Chain> HasChainTypes for Chain where
    Chain: HasHeightType
        + HasMessageType
        + HasEventType
        + HasChainIdType
        + HasTimestampType
        + HasErrorType
{
}
