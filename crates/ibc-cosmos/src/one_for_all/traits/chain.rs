use crate::types::event::IbcEvent;
use core::time::Duration;
use ibc::core::ics02_client::client_type::ClientType;
use ibc::core::ics24_host::identifier::ClientId;
use ibc::timestamp::Timestamp;
use ibc::Height;
use ibc_framework::core::traits::client::{HasAnyClientMethods, HasAnyClientTypes};
use ibc_framework::core::traits::sync::Async;

use crate::types::message::IbcMessageType;

pub trait OfaCosmosChain: Async {
    type Error: Async;

    type ChainComponents;

    type AnyClient: HasAnyClientMethods<
        Timestamp = Timestamp,
        Height = Height,
        Duration = Duration,
        ClientType = ClientType,
    >;

    fn emit_event(&self, event: &IbcEvent<Self::AnyClient>);

    fn host_height(&self) -> Height;

    fn host_timestamp(&self) -> Timestamp;

    fn get_client_type(&self, client_id: &ClientId) -> Result<ClientType, Self::Error>;

    fn get_any_client_state(
        &self,
        client_id: &ClientId,
    ) -> Result<<Self::AnyClient as HasAnyClientTypes>::AnyClientState, Self::Error>;

    fn get_latest_any_consensus_state(
        &self,
        client_id: &ClientId,
    ) -> Result<<Self::AnyClient as HasAnyClientTypes>::AnyConsensusState, Self::Error>;

    fn get_any_consensus_state_at_height(
        &self,
        client_id: &ClientId,
        height: &Height,
    ) -> Result<Option<<Self::AnyClient as HasAnyClientTypes>::AnyConsensusState>, Self::Error>;

    fn get_any_consensus_state_after_height(
        &self,
        client_id: &ClientId,
        height: &Height,
    ) -> Result<Option<<Self::AnyClient as HasAnyClientTypes>::AnyConsensusState>, Self::Error>;

    fn get_any_consensus_state_before_height(
        &self,
        client_id: &ClientId,
        height: &Height,
    ) -> Result<Option<<Self::AnyClient as HasAnyClientTypes>::AnyConsensusState>, Self::Error>;

    fn set_any_client_state(
        &self,
        client_id: &ClientId,
        client_state: &<Self::AnyClient as HasAnyClientTypes>::AnyClientState,
    ) -> Result<(), Self::Error>;

    fn set_any_consensus_state(
        &self,
        client_id: &ClientId,
        consensus_state: &<Self::AnyClient as HasAnyClientTypes>::AnyConsensusState,
    ) -> Result<(), Self::Error>;

    fn client_type_mismatch_error(expected_client_type: &ClientType) -> Self::Error;

    fn unknown_message_error(message_type: &IbcMessageType) -> Self::Error;

    fn parse_message_error(message_type: &IbcMessageType) -> Self::Error;

    fn client_frozen_error(client_id: &ClientId) -> Self::Error;

    fn client_expired_error(
        client_id: &ClientId,
        current_time: &Timestamp,
        latest_allowed_update_time: &Timestamp,
    ) -> Self::Error;
}
