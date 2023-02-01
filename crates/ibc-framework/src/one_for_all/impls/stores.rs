use crate::core::traits::stores::client_reader::AnyClientReader;
use crate::core::traits::stores::client_writer::AnyClientWriter;
use crate::one_for_all::traits::chain::OfaChain;
use crate::one_for_all::types::chain::OfaChainWrapper;

pub struct OfaClientReader;
pub struct OfaClientWriter;

impl<Chain> AnyClientReader<OfaChainWrapper<Chain>> for OfaClientReader
where
    Chain: OfaChain,
{
    fn get_client_type(
        context: &OfaChainWrapper<Chain>,
        client_id: &Chain::ClientId,
    ) -> Result<Chain::ClientType, Chain::Error> {
        context.chain.get_client_type(client_id)
    }

    fn get_any_client_state(
        context: &OfaChainWrapper<Chain>,
        client_id: &Chain::ClientId,
    ) -> Result<Chain::AnyClientState, Chain::Error> {
        context.chain.get_any_client_state(client_id)
    }

    fn get_latest_any_consensus_state(
        context: &OfaChainWrapper<Chain>,
        client_id: &Chain::ClientId,
    ) -> Result<Chain::AnyConsensusState, Chain::Error> {
        context.chain.get_latest_any_consensus_state(client_id)
    }

    fn get_any_consensus_state_at_height(
        context: &OfaChainWrapper<Chain>,
        client_id: &Chain::ClientId,
        height: &Chain::Height,
    ) -> Result<Option<Chain::AnyConsensusState>, Chain::Error> {
        context
            .chain
            .get_any_consensus_state_at_height(client_id, height)
    }

    fn get_any_consensus_state_after_height(
        context: &OfaChainWrapper<Chain>,
        client_id: &Chain::ClientId,
        height: &Chain::Height,
    ) -> Result<Option<Chain::AnyConsensusState>, Chain::Error> {
        context
            .chain
            .get_any_consensus_state_after_height(client_id, height)
    }

    fn get_any_consensus_state_before_height(
        context: &OfaChainWrapper<Chain>,
        client_id: &Chain::ClientId,
        height: &Chain::Height,
    ) -> Result<Option<Chain::AnyConsensusState>, Chain::Error> {
        context
            .chain
            .get_any_consensus_state_before_height(client_id, height)
    }
}

impl<Chain> AnyClientWriter<OfaChainWrapper<Chain>> for OfaClientWriter
where
    Chain: OfaChain,
{
    fn set_any_client_state(
        context: &OfaChainWrapper<Chain>,
        client_id: &Chain::ClientId,
        client_state: &Chain::AnyClientState,
    ) -> Result<(), Chain::Error> {
        context.chain.set_any_client_state(client_id, client_state)
    }

    fn set_any_consensus_state(
        context: &OfaChainWrapper<Chain>,
        client_id: &Chain::ClientId,
        consensus_state: &Chain::AnyConsensusState,
    ) -> Result<(), Chain::Error> {
        context
            .chain
            .set_any_consensus_state(client_id, consensus_state)
    }
}
