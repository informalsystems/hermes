/*!
   Constructs for the chain context.

   A chain context corresponds to the context that the relayer uses to
   interact with a single chain. For the purpose of the relayer, the
   chain context acts as a _client_ to the chain. This is in contrast
   with other provider-side chain constructs, which are used for implementing
   a blockchain, and are not covered by this chain context.

   At its core, a chain context should implement
   [`HasChainTypes`](traits::types::chain::HasChainTypes), which declares the abstract
   types that are commonly used inside a chain context.

   The chain context provides functionalities for querying the chain,
   such as through [`CanQueryChainStatus`](traits::queries::status::CanQueryChainStatus).
   It also supports sending of messages to a chain using
   [`CanSendMessages`](traits::message_sender::CanSendMessages).

   ## List of Traits

   Here is a non-comprehensive list of chain traits that are defined in this module:

   ### Type Traits

   - Chain types:
      - [`HasChainTypes`](traits::types::chain::HasChainTypes)
      - [`HasHeightType`](traits::types::height::HasHeightType)
      - [`HasMessageType`](traits::types::message::HasMessageType)
      - [`HasEventType`](traits::types::event::HasEventType)
      - [`HasChainIdType`](traits::types::chain_id::HasChainIdType)
      - [`HasTimestampType`](traits::types::timestamp::HasTimestampType)
      - [`HasChainStatusType`](traits::types::status::HasChainStatusType)
      - [`HasConsensusStateType`](traits::types::consensus_state::HasConsensusStateType)
   - IBC chain types:
      - [`HasIbcChainTypes`](traits::types::ibc::HasIbcChainTypes)
      - [`HasIbcPacketTypes`](traits::types::packet::HasIbcPacketTypes)
   - IBC events:
      - [`HasWriteAcknowledgementEvent`](traits::types::ibc_events::write_ack::HasWriteAcknowledgementEvent)
      - [`HasSendPacketEvent`](traits::types::ibc_events::send_packet::HasSendPacketEvent)

   ### Consumer Traits

   - Chain methods:
      - [`HasChainId`](traits::types::chain_id::HasChainId)
      - [`CanSendMessages`](traits::message_sender::CanSendMessages)
      - [`CanEstimateMessageSize`](traits::types::message::CanEstimateMessageSize)
      - [`HasCounterpartyMessageHeight`](traits::types::ibc::HasCounterpartyMessageHeight)
   - Message builders:
      - [`CanBuildAckPacketMessage`](traits::message_builders::ack_packet::CanBuildAckPacketMessage)
      - [`CanBuildReceivePacketMessage`](traits::message_builders::receive_packet::CanBuildReceivePacketMessage)
      - [`CanBuildTimeoutUnorderedPacketMessage`](traits::message_builders::timeout_unordered_packet::CanBuildTimeoutUnorderedPacketMessage)
   - Chain queries:
      - [`CanQueryChainStatus`](traits::queries::status::CanQueryChainStatus)
      - [`CanQueryConsensusState`](traits::queries::consensus_state::CanQueryConsensusState)
      - [`CanQueryReceivedPacket`](traits::queries::received_packet::CanQueryReceivedPacket)
      - [`CanQueryCounterpartyChainIdFromChannel`](traits::queries::channel::CanQueryCounterpartyChainIdFromChannel)
      - [`CanQueryWriteAcknowledgement`](traits::queries::write_ack::CanQueryWriteAcknowledgement)

   ### Provider Traits

   - [`MessageSender`](traits::message_sender::MessageSender)
   - [`ChainStatusQuerier`](traits::queries::status::ChainStatusQuerier)
   - [`ConsensusStateQuerier`](traits::queries::consensus_state::ConsensusStateQuerier)
   - [`ReceivedPacketQuerier`](traits::queries::received_packet::ReceivedPacketQuerier)
*/

pub mod traits;
pub mod types;
