use core::time::Duration;
use ibc::core::ics02_client::client_type::ClientType;
use ibc::core::ics23_commitment::merkle::MerkleProof;
use ibc::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use ibc::signer::Signer;
use ibc::timestamp::Timestamp;
use ibc::Height;
use ibc_framework::core::traits::client::HasAnyClientMethods;
use ibc_framework::core::traits::client::HasAnyClientTypes;
use ibc_framework::one_for_all::components::default::DefaultChainComponents;
use ibc_framework::one_for_all::traits::chain::{OfaChain, OfaChainTypes};

use crate::one_for_all::traits::chain::OfaCosmosChain;
use crate::one_for_all::types::chain::OfaCosmosChainWrapper;
use crate::types::event::IbcEvent;
use crate::types::message::{IbcMessage, IbcMessageType, UpdateClientMessage};

impl<Chain> OfaChainTypes for OfaCosmosChainWrapper<Chain>
where
    Chain: OfaCosmosChain,
{
    type Error = Chain::Error;

    type Event = IbcEvent<Chain::AnyClient>;

    type Height = Height;

    type Timestamp = Timestamp;

    type Duration = Duration;

    type Message = IbcMessage<Chain::AnyClient>;

    type MessageType = IbcMessageType;

    type Signer = Signer;

    type ClientId = ClientId;

    type ConnectionId = ConnectionId;

    type ChannelId = ChannelId;

    type Port = PortId;

    type MerkleProof = MerkleProof;

    type ClientType = ClientType;

    type AnyClientState = <Chain::AnyClient as HasAnyClientTypes>::AnyClientState;

    type AnyConsensusState = <Chain::AnyClient as HasAnyClientTypes>::AnyConsensusState;

    type AnyClientHeader = <Chain::AnyClient as HasAnyClientTypes>::AnyClientHeader;

    type AnyMisbehavior = <Chain::AnyClient as HasAnyClientTypes>::AnyMisbehavior;

    type UpdateClientMessage = UpdateClientMessage<Chain::AnyClient>;
}

#[allow(unused_variables)]
impl<Chain> OfaChain for OfaCosmosChainWrapper<Chain>
where
    Chain: OfaCosmosChain,
{
    type ChainComponents = DefaultChainComponents;

    type ClientComponents = Chain::AnyClient;

    fn emit_event(&self, event: &Self::Event) {
        self.chain.emit_event(event)
    }

    fn host_height(&self) -> Height {
        self.chain.host_height()
    }

    fn host_timestamp(&self) -> Timestamp {
        self.chain.host_timestamp()
    }

    fn add_duration(time: &Timestamp, duration: &Duration) -> Timestamp {
        (*time + *duration).unwrap()
    }

    fn message_type(message: &Self::Message) -> IbcMessageType {
        message.message_type()
    }

    fn client_state_type(client_state: &Self::AnyClientState) -> Self::ClientType {
        Chain::AnyClient::client_state_type(client_state)
    }

    fn client_state_is_frozen(client_state: &Self::AnyClientState) -> bool {
        Chain::AnyClient::client_state_is_frozen(client_state)
    }

    fn client_state_trusting_period(client_state: &Self::AnyClientState) -> Duration {
        Chain::AnyClient::client_state_trusting_period(client_state)
    }

    fn client_state_latest_height(client_state: &Self::AnyClientState) -> Height {
        Chain::AnyClient::client_state_latest_height(client_state)
    }

    fn consensus_state_timestamp(consensus_state: &Self::AnyConsensusState) -> Timestamp {
        Chain::AnyClient::consensus_state_timestamp(consensus_state)
    }

    fn client_header_height(client_header: &Self::AnyClientHeader) -> Height {
        Chain::AnyClient::client_header_height(client_header)
    }

    fn get_client_type(&self, client_id: &ClientId) -> Result<ClientType, Self::Error> {
        self.chain.get_client_type(client_id)
    }

    fn get_any_client_state(
        &self,
        client_id: &ClientId,
    ) -> Result<Self::AnyClientState, Self::Error> {
        self.chain.get_any_client_state(client_id)
    }

    fn get_latest_any_consensus_state(
        &self,
        client_id: &ClientId,
    ) -> Result<Self::AnyConsensusState, Self::Error> {
        self.chain.get_latest_any_consensus_state(client_id)
    }

    fn get_any_consensus_state_at_height(
        &self,
        client_id: &ClientId,
        height: &Height,
    ) -> Result<Option<Self::AnyConsensusState>, Self::Error> {
        self.chain
            .get_any_consensus_state_at_height(client_id, height)
    }

    fn get_any_consensus_state_after_height(
        &self,
        client_id: &ClientId,
        height: &Height,
    ) -> Result<Option<Self::AnyConsensusState>, Self::Error> {
        self.chain
            .get_any_consensus_state_after_height(client_id, height)
    }

    fn get_any_consensus_state_before_height(
        &self,
        client_id: &ClientId,
        height: &Height,
    ) -> Result<Option<Self::AnyConsensusState>, Self::Error> {
        self.chain
            .get_any_consensus_state_before_height(client_id, height)
    }

    fn set_any_client_state(
        &self,
        client_id: &ClientId,
        client_state: &Self::AnyClientState,
    ) -> Result<(), Self::Error> {
        self.chain.set_any_client_state(client_id, client_state)
    }

    fn set_any_consensus_state(
        &self,
        client_id: &ClientId,
        consensus_state: &Self::AnyConsensusState,
    ) -> Result<(), Self::Error> {
        self.chain
            .set_any_consensus_state(client_id, consensus_state)
    }

    fn client_type_mismatch_error(expected_client_type: &ClientType) -> Self::Error {
        Chain::client_type_mismatch_error(expected_client_type)
    }

    fn unknown_message_error(message_type: &IbcMessageType) -> Self::Error {
        Chain::unknown_message_error(message_type)
    }

    fn parse_message_error(message_type: &IbcMessageType) -> Self::Error {
        Chain::parse_message_error(message_type)
    }

    fn client_frozen_error(client_id: &ClientId) -> Self::Error {
        Chain::client_frozen_error(client_id)
    }

    fn client_expired_error(
        client_id: &ClientId,
        current_time: &Timestamp,
        latest_allowed_update_time: &Timestamp,
    ) -> Self::Error {
        Chain::client_expired_error(client_id, current_time, latest_allowed_update_time)
    }

    fn update_client_event(
        client_id: &ClientId,
        client_type: &ClientType,
        consensus_height: &Height,
        header: &Self::AnyClientHeader,
    ) -> Self::Event {
        todo!()
    }

    fn misbehavior_event(
        client_id: &Self::ClientId,
        client_type: &Self::ClientType,
        consensus_height: &Self::Height,
        header: &Self::AnyClientHeader,
    ) -> Self::Event {
        todo!()
    }

    const UPDATE_CLIENT_MESSAGE_TYPE: IbcMessageType = IbcMessageType::UpdateClient;

    fn try_extract_update_client_message(
        message: &IbcMessage<Chain::AnyClient>,
    ) -> Option<&Self::UpdateClientMessage> {
        match message {
            IbcMessage::UpdateClient(message) => Some(message),
        }
    }

    fn update_client_message_client_id(message: &Self::UpdateClientMessage) -> &ClientId {
        &message.client_id
    }

    fn update_client_message_client_header(
        message: &Self::UpdateClientMessage,
    ) -> &Self::AnyClientHeader {
        &message.client_header
    }
}
