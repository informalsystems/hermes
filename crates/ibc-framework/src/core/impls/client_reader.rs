use crate::core::traits::client::{ContainsClient, HasClientTypeFor, HasClientTypes};
use crate::core::traits::stores::client_reader::{ClientReader, HasAnyClientReader};

pub struct ClientReaderFromAnyClient;

impl<Context, Client> ClientReader<Context, Client> for ClientReaderFromAnyClient
where
    Client: HasClientTypes,
    Context: HasAnyClientReader + ContainsClient<Client> + HasClientTypeFor<Client>,
{
    fn get_client_state(
        context: &Context,
        client_id: &Context::ClientId,
    ) -> Result<Client::ClientState, Context::Error> {
        let any_client_state = context.get_any_client_state(client_id)?;

        let client_state = Context::try_from_any_client_state(any_client_state)?;

        Ok(client_state)
    }

    fn get_latest_consensus_state(
        context: &Context,
        client_id: &Context::ClientId,
    ) -> Result<Client::ConsensusState, Context::Error> {
        let any_consensus_state = context.get_latest_any_consensus_state(client_id)?;

        let consensus_state = Context::try_from_any_consensus_state(any_consensus_state)?;

        Ok(consensus_state)
    }

    fn get_consensus_state_at_height(
        context: &Context,
        client_id: &Context::ClientId,
        height: &Context::Height,
    ) -> Result<Option<Client::ConsensusState>, Context::Error> {
        let m_consensus_state = context.get_any_consensus_state_at_height(client_id, height)?;

        match m_consensus_state {
            Some(any_consensus_state) => {
                let consensus_state = Context::try_from_any_consensus_state(any_consensus_state)?;

                Ok(Some(consensus_state))
            }
            None => Ok(None),
        }
    }

    fn get_consensus_state_after_height(
        context: &Context,
        client_id: &Context::ClientId,
        height: &Context::Height,
    ) -> Result<Option<Client::ConsensusState>, Context::Error> {
        let m_consensus_state = context.get_any_consensus_state_after_height(client_id, height)?;

        match m_consensus_state {
            Some(any_consensus_state) => {
                let consensus_state = Context::try_from_any_consensus_state(any_consensus_state)?;

                Ok(Some(consensus_state))
            }
            None => Ok(None),
        }
    }

    fn get_consensus_state_before_height(
        context: &Context,
        client_id: &Context::ClientId,
        height: &Context::Height,
    ) -> Result<Option<Client::ConsensusState>, Context::Error> {
        let m_consensus_state = context.get_any_consensus_state_before_height(client_id, height)?;

        match m_consensus_state {
            Some(any_consensus_state) => {
                let consensus_state = Context::try_from_any_consensus_state(any_consensus_state)?;

                Ok(Some(consensus_state))
            }
            None => Ok(None),
        }
    }
}
