/*!
   Constructs for the chain context.

   A chain context corresponds to the context that the relayer uses to
   interact with a single chain. For the purpose of the relayer, the
   chain context acts as a _client_ to the chain. This is in contrast
   with other provider-side chain constructs, which are used for implementing
   a blockchain, and are not covered by this chain context.

   At its core, a chain context should implement
   [`HasChainTypes`](traits::types::HasChainTypes), which declares the abstract
   types that are commonly used inside a chain context.

   The chain context provides functionalities for querying the chain,
   such as through [`CanQueryChainStatus`](traits::queries::status::CanQueryChainStatus).
   It also supports sending of messages to a chain using
   [`CanSendMessages`](traits::message_sender::CanSendMessages).

   ## All-In-One Traits

   The provider-side closure of the chain components defined in this module
   is captured by the one-for-all trait
   [`OfaBaseChain`](crate::base::one_for_all::traits::chain::OfaBaseChain).
   That allows users to implement all chain context traits in this module
   by implementing the one-for-all chain context traits.

   The consumer-side closure of the chain components defined in this module
   is captured by the all-for-one trait
   [`AfoBaseChain`](crate::base::all_for_one::chain::AfoBaseChain).
   That allows users to consume all chain context methods in this module
   by adding `Chain: AfoBaseChain` to the `where` clause.

   ## List of Traits

   Here is a shortcut list of chain traits that are defined in this module:

   Type traits:

   - [`HasMessageType`](traits::types::HasMessageType)
   - [`HasEventType`](traits::types::HasEventType)
   - [`HasChainTypes`](traits::types::HasChainTypes)
   - [`HasIbcChainTypes`](traits::types::HasIbcChainTypes)
   - [`HasWriteAcknowledgementEvent`](traits::ibc_event::HasWriteAcknowledgementEvent)
   - [`HasChainStatus`](traits::queries::status::HasChainStatus)
   - [`HasConsensusState`](traits::queries::consensus_state::HasConsensusState)

   Consumer traits:

   - [`CanSendMessages`](traits::message_sender::CanSendMessages)
   - [`CanQueryChainStatus`](traits::queries::status::CanQueryChainStatus)
   - [`CanQueryConsensusState`](traits::queries::consensus_state::CanQueryConsensusState)
   - [`CanQueryReceivedPacket`](traits::queries::received_packet::CanQueryReceivedPacket)

   Provider traits:

   - [`MessageSender`](traits::message_sender::MessageSender)
   - [`ChainStatusQuerier`](traits::queries::status::ChainStatusQuerier)
   - [`ConsensusStateQuerier`](traits::queries::consensus_state::ConsensusStateQuerier)
   - [`ReceivedPacketQuerier`](traits::queries::received_packet::ReceivedPacketQuerier)
*/

pub mod traits;
pub mod types;
