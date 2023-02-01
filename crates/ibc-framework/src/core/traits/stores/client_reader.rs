use crate::core::traits::client::{ContainsClient, HasAnyClientTypes, HasClientTypes};
use crate::core::traits::error::HasError;
use crate::core::traits::host::HasHostTypes;
use crate::core::traits::ibc::HasIbcTypes;

pub trait AnyClientReader<Context>
where
    Context: HasAnyClientTypes + HasIbcTypes + HasHostTypes + HasError,
{
    fn get_client_type(
        context: &Context,
        client_id: &Context::ClientId,
    ) -> Result<Context::ClientType, Context::Error>;

    fn get_any_client_state(
        context: &Context,
        client_id: &Context::ClientId,
    ) -> Result<Context::AnyClientState, Context::Error>;

    fn get_latest_any_consensus_state(
        context: &Context,
        client_id: &Context::ClientId,
    ) -> Result<Context::AnyConsensusState, Context::Error>;

    fn get_any_consensus_state_at_height(
        context: &Context,
        client_id: &Context::ClientId,
        height: &Context::Height,
    ) -> Result<Option<Context::AnyConsensusState>, Context::Error>;

    fn get_any_consensus_state_after_height(
        context: &Context,
        client_id: &Context::ClientId,
        height: &Context::Height,
    ) -> Result<Option<Context::AnyConsensusState>, Context::Error>;

    fn get_any_consensus_state_before_height(
        context: &Context,
        client_id: &Context::ClientId,
        height: &Context::Height,
    ) -> Result<Option<Context::AnyConsensusState>, Context::Error>;
}

pub trait HasAnyClientReader: HasAnyClientTypes + HasIbcTypes + HasHostTypes + HasError {
    type AnyClientReader: AnyClientReader<Self>;

    fn get_client_type(&self, client_id: &Self::ClientId) -> Result<Self::ClientType, Self::Error> {
        Self::AnyClientReader::get_client_type(self, client_id)
    }

    fn get_any_client_state(
        &self,
        client_id: &Self::ClientId,
    ) -> Result<Self::AnyClientState, Self::Error> {
        Self::AnyClientReader::get_any_client_state(self, client_id)
    }

    fn get_latest_any_consensus_state(
        &self,
        client_id: &Self::ClientId,
    ) -> Result<Self::AnyConsensusState, Self::Error> {
        Self::AnyClientReader::get_latest_any_consensus_state(self, client_id)
    }

    fn get_any_consensus_state_at_height(
        &self,
        client_id: &Self::ClientId,
        height: &Self::Height,
    ) -> Result<Option<Self::AnyConsensusState>, Self::Error> {
        Self::AnyClientReader::get_any_consensus_state_at_height(self, client_id, height)
    }

    fn get_any_consensus_state_after_height(
        &self,
        client_id: &Self::ClientId,
        height: &Self::Height,
    ) -> Result<Option<Self::AnyConsensusState>, Self::Error> {
        Self::AnyClientReader::get_any_consensus_state_after_height(self, client_id, height)
    }

    fn get_any_consensus_state_before_height(
        &self,
        client_id: &Self::ClientId,
        height: &Self::Height,
    ) -> Result<Option<Self::AnyConsensusState>, Self::Error> {
        Self::AnyClientReader::get_any_consensus_state_after_height(self, client_id, height)
    }
}

pub struct MismatchClientFormat<ClientType> {
    pub expected_client_type: ClientType,
}

pub trait ClientReader<Context, Client>
where
    Context: HasError + HasIbcTypes + HasHostTypes + ContainsClient<Client>,
    Client: HasClientTypes,
{
    fn get_client_state(
        context: &Context,
        client_id: &Context::ClientId,
    ) -> Result<Client::ClientState, Context::Error>;

    fn get_latest_consensus_state(
        context: &Context,
        client_id: &Context::ClientId,
    ) -> Result<Client::ConsensusState, Context::Error>;

    fn get_consensus_state_at_height(
        context: &Context,
        client_id: &Context::ClientId,
        height: &Context::Height,
    ) -> Result<Option<Client::ConsensusState>, Context::Error>;

    fn get_consensus_state_after_height(
        context: &Context,
        client_id: &Context::ClientId,
        height: &Context::Height,
    ) -> Result<Option<Client::ConsensusState>, Context::Error>;

    fn get_consensus_state_before_height(
        context: &Context,
        client_id: &Context::ClientId,
        height: &Context::Height,
    ) -> Result<Option<Client::ConsensusState>, Context::Error>;
}

pub trait HasClientReader<Client>:
    HasError + HasIbcTypes + HasHostTypes + ContainsClient<Client>
where
    Client: HasClientTypes,
{
    type ClientReader: ClientReader<Self, Client>;

    fn get_client_state(
        &self,
        client_id: &Self::ClientId,
    ) -> Result<Client::ClientState, Self::Error> {
        Self::ClientReader::get_client_state(self, client_id)
    }

    fn get_latest_consensus_state(
        &self,
        client_id: &Self::ClientId,
    ) -> Result<Client::ConsensusState, Self::Error> {
        Self::ClientReader::get_latest_consensus_state(self, client_id)
    }

    fn get_consensus_state_at_height(
        &self,
        client_id: &Self::ClientId,
        height: &Self::Height,
    ) -> Result<Option<Client::ConsensusState>, Self::Error> {
        Self::ClientReader::get_consensus_state_at_height(self, client_id, height)
    }

    fn get_consensus_state_after_height(
        &self,
        client_id: &Self::ClientId,
        height: &Self::Height,
    ) -> Result<Option<Client::ConsensusState>, Self::Error> {
        Self::ClientReader::get_consensus_state_after_height(self, client_id, height)
    }

    fn get_consensus_state_before_height(
        &self,
        client_id: &Self::ClientId,
        height: &Self::Height,
    ) -> Result<Option<Client::ConsensusState>, Self::Error> {
        Self::ClientReader::get_consensus_state_before_height(self, client_id, height)
    }
}
