use crate::core::ics02_client::client_consensus::ConsensusState;
use crate::error::Error;

use super::crypto_ops::NearCryptoOps;
pub struct NearConsensusState {}

impl ConsensusState for NearConsensusState {
    type Error = Error;

    type Crypto = NearCryptoOps;

    fn client_type(&self) -> crate::core::ics02_client::client_type::ClientType {
        todo!()
    }

    fn root(&self) -> &crate::core::ics23_commitment::commitment::CommitmentRoot {
        todo!()
    }

    fn wrap_any(
        self,
    ) -> crate::core::ics02_client::client_consensus::AnyConsensusState<Self::Crypto> {
        todo!()
    }
}
