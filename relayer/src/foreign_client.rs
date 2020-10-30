use prost_types::Any;
use tendermint::{block::signed_header::SignedHeader, Hash};
use thiserror::Error;

use ibc::{
    ics02_client::{header::Header, msgs::MsgCreateAnyClient},
    ics07_tendermint::consensus_state::ConsensusState,
    ics23_commitment::commitment::CommitmentProof,
    ics24_host::identifier::{ChainId, ClientId},
    ics24_host::Path::ClientState as ClientStatePath,
    Height,
};

use crate::chain::handle::ChainHandle;
use crate::msgs::Datagram;
use ibc::ics02_client::client_def::AnyConsensusState;

#[derive(Debug, Error)]
pub enum ForeignClientError {
    #[error("error raised while creating client: {0}")]
    ClientCreation(String),
}

#[derive(Clone)]
pub struct ForeignClientConfig {
    id: ClientId,
    // create_timeout: Duration // How much to wait before giving up on client creation.
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
    /// TODO: pre-conditions for success?
    /// Is it enough to have a "live" handle to each of `host` and `target` chains?
    pub fn new(
        host: &dyn ChainHandle,
        source: &dyn ChainHandle,
        config: ForeignClientConfig,
    ) -> Result<ForeignClient, ForeignClientError> {
        // Query the client state on source chain.
        let response = host.query(ClientStatePath(config.clone().id), Height::zero(), false);

        // The chain may already host a client with this id.
        if response.is_ok() {
            Ok(ForeignClient { config }) // Nothing left to do.
        } else {
            // Create a new client on the host chain.
            Self::create_client(host, source)?;
            // Now subscribe and wait at most `config.create_timeout` to confirm the success.
            // dst.subscribe();
            Ok(ForeignClient { config })
        }
    }

    /// Creates on the `dst` chain an IBC client which will store headers for `src` chain.
    fn create_client(
        dst: &dyn ChainHandle, // The chain that will host the client.
        src: &dyn ChainHandle, // The client will store headers of this chain.
    ) -> Result<(), ForeignClientError> {
        // Fetch latest header of the source chain.
        let latest_header = src.get_header(Height::zero()).map_err(|e| {
            ForeignClientError::ClientCreation(format!("failed to fetch latest header ({:?})", e))
        })?;

        // Build the consensus state.
        // The destination chain handle knows the internals of assembling this message.
        // let consensus_state =
        //     AnyConsensusState::Tendermint(tm_consensus_state);
        //     tm_latest_header.signed_header,
        // );

        // let tm_consensus_state = dst.
        //     ibc::ics07_tendermint::consensus_state::ConsensusState::from(
        //     tm_latest_header.signed_header,
        // );

        // Build the client state. Destination chain handle will take care of the details.

        // Create a proto any message.
        let proto_msgs = vec![Any {
            // TODO - add get_url_type() to prepend proper string to get_type()
            type_url: "/ibc.client.MsgCreateClient".to_ascii_lowercase(),
            value: vec![], //new_msg.get_sign_bytes(),
        }];

        // TODO: Bridge from Any message into EncodedTransaction.
        // dst.submit(&proto_msgs)?

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
