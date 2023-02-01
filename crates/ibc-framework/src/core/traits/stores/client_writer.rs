use crate::core::traits::client::HasAnyClientTypes;
use crate::core::traits::error::HasError;
use crate::core::traits::ibc::HasIbcTypes;

pub trait AnyClientWriter<Context>
where
    Context: HasAnyClientTypes + HasIbcTypes + HasError,
{
    fn set_any_client_state(
        context: &Context,
        client_id: &Context::ClientId,
        client_state: &Context::AnyClientState,
    ) -> Result<(), Context::Error>;

    fn set_any_consensus_state(
        context: &Context,
        client_id: &Context::ClientId,
        consensus_state: &Context::AnyConsensusState,
    ) -> Result<(), Context::Error>;
}

pub trait HasAnyClientWriter: HasAnyClientTypes + HasIbcTypes + HasError {
    type AnyClientWriter: AnyClientWriter<Self>;

    fn set_any_client_state(
        &self,
        client_id: &Self::ClientId,
        client_state: &Self::AnyClientState,
    ) -> Result<(), Self::Error> {
        Self::AnyClientWriter::set_any_client_state(self, client_id, client_state)
    }

    fn set_any_consensus_state(
        &self,
        client_id: &Self::ClientId,
        consensus_state: &Self::AnyConsensusState,
    ) -> Result<(), Self::Error> {
        Self::AnyClientWriter::set_any_consensus_state(self, client_id, consensus_state)
    }
}
