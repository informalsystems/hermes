use tendermint::{block::signed_header::SignedHeader, Hash};
use thiserror::Error;

use ibc::{
    ics07_tendermint::consensus_state::ConsensusState,
    ics23_commitment::commitment::CommitmentProof,
    ics24_host::identifier::{ChainId, ClientId},
    ics24_host::Path::ClientState as ClientStatePath,
    Height,
};

use crate::chain::handle::ChainHandle;
use crate::msgs::Datagram;

#[derive(Debug, Error)]
pub enum ForeignClientError {
    #[error("error raised while creating client: {0}")]
    ClientCreation(String),
}

#[derive(Clone)]
pub struct ForeignClientConfig {
    id: ClientId,
    // timeout: Duration // How much to wait before giving up on client creation.
}

impl ForeignClientConfig {
    pub fn new(client_id: ClientId) -> ForeignClientConfig {
        Self { id: client_id }
    }

    pub fn client_id(&self) -> &ClientId {
        &self.id
    }
}

pub struct ForeignClient {
    config: ForeignClientConfig,
}

impl ForeignClient {
    /// Creates a new foreign client.
    /// Post-condition: chain `host` will host an IBC client for chain `source`.
    /// TODO: pre-conditions for success: live handle to each of `host` and `target` chains enough?
    pub fn new(
        host: &dyn ChainHandle,
        source: &dyn ChainHandle,
        config: ForeignClientConfig,
    ) -> Result<ForeignClient, ForeignClientError> {
        // Query the client state on source chain.
        let response = host.query(ClientStatePath(config.clone().id), Height::zero(), false);
        if response.is_ok() {
            // The chain already hosts a client with the required id.
            Ok(ForeignClient { config })
        } else {
            Self::create_client(host, source)?;
            // Create a new client
            Ok(ForeignClient { config })
        }
    }

    fn create_client(
        dst: &dyn ChainHandle, // The chain that will host the client.
        src: &dyn ChainHandle, // The client will store headers of this chain.
    ) -> Result<(), ForeignClientError> {
        let latest_header = src.get_header(Height::zero()).map_err(|e| {
            ForeignClientError::ClientCreation(format!(
                "failed to fetch latest header ({:?})",
                e
            ))
        })?;

        Ok(())
    }

    // This is a completely different synchronous update strategy then bundeling a an update packet
    pub fn update(
        &mut self,
        src_chain: &dyn ChainHandle,
        dst_chain: &dyn ChainHandle,
        src_target_height: Height,
    ) -> Result<Height, ForeignClientError> {
        /*
        return Ok(src_target_height);
        let (src_consensus_state, dst_membership_proof) =
            dst_chain.consensus_state(src_chain.id(), src_target_height);

        let dst_sh = dst_chain.get_header(dst_membership_proof.height + 1);
        // type verifyMembership = (root: CommitmentRoot, proof: CommitmentProof, path: CommitmentPath, value: Value) => boolean (ICS-023)
        if ! verify_consensus_state_inclusion(&src_consensus_state, &dst_membership_proof, &(dst_sh.header.app_hash)) {
            // Error: Destination chain provided invalid consensus_state
            return Err(ForeignClientError::VerificationError())
        }

        if src_chain.get_header(src_consensus_state.height).header == src_consensus_state.signed_header.header {
            return Err(ForeignClientError::HeaderMismatch())
        }

        while src_consensus_state.height < src_target_height {
            let src_signed_headers = src_chain.get_minimal_set(src_consensus_state.height, src_target_height);

            // if we actually want to do this we need to create a transaction
            // This might fail semantically due to competing relayers
            // Even if this fails, we need to continue
            // XXX FIXME
            dst_chain.submit(vec![create_client_update_datagram(src_signed_headers)]);

            let (src_consensus_state, dst_membership_proof) = dst_chain.consensus_state(src_chain.id(), src_target_height);
            let dst_sh = dst_chain.get_header(dst_membership_proof.height + 1);
            if ! verify_consensus_state_inclusion(&src_consensus_state, &dst_membership_proof, &(dst_sh.header.app_hash)) {
                // Error: Destination chain provided invalid client_state
                return Err(ForeignClientError::VerificationError())
            }

            if src_chain.get_header(src_consensus_state.height).header == src_consensus_state.signed_header.header {
                // Error: consesus_state isn't verified by self light client
                return  Err(ForeignClientError::HeaderMismatch())
            }
        }
        */

        Ok(src_target_height)
    }
}

fn verify_consensus_state_inclusion(
    _consensus_state: &ConsensusState,
    _membership_proof: &CommitmentProof,
    _hash: &Hash,
) -> bool {
    true
}

// XXX: It's probably the link that can produce this
fn create_client_update_datagram(_header: Vec<SignedHeader>) -> Datagram {
    Datagram::NoOp()
}
