use crate::types::{Height, Hash, ChainId, ChannelId, ClientId, PortId, Datagram};
use crate::connection::ConnectionError;
use crate::channel::{Channel, ChannelError};
use crate::foreign_client::{ForeignClient, ForeignClientError};
use crate::chain::{Chain, ChainError, SignedHeader, MembershipProof, ConsensusState};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum LinkError {
    #[error("NoOp")]
    NoOp(),

    #[error("Verificaiton failed")]
    VerificationError(),

    #[error("Headers didn't match")]
    HeaderMismatch(),

    #[error("Chain error")]
    ChainError(#[from] ChainError),

    #[error("Foreign client error")]
    ForeignClientError(#[from] ForeignClientError),

    #[error("ConnectionError:")]
    ConnectionError(#[from] ConnectionError),

    #[error("ChannelError:")]
    ChannelError(#[from] ChannelError),
}

enum Order {
    Ordered(),
    Unordered(),
}

struct ConfigSide {
    chain_id: ChainId,
    client_id: ClientId,
    channel_id: ChannelId,
    port_id: PortId,
}

pub struct LinkConfig {
    src_config: ConfigSide,
    dst_config: ConfigSide,
    order: Order,
}

impl LinkConfig {
    pub fn default() -> LinkConfig {
        return LinkConfig {
            src_config: ConfigSide {
                port_id: "".to_string(),
                channel_id: "".to_string(),
                chain_id: 0,
                client_id: "".to_string(),
            },
            dst_config: ConfigSide {
                port_id: "".to_string(),
                channel_id: "".to_string(),
                chain_id: 0,
                client_id: "".to_string(),
            },
            order: Order::Unordered(),
        }
    }
}

pub struct Link {
    pub src_chain: Box<dyn Chain>, // XXX: Can these be private?
    pub dst_chain: Box<dyn Chain>,
    foreign_client: ForeignClient,
}

impl Link {
    pub fn new(
        src_chain: impl Chain + 'static,
        dst_chain: impl Chain + 'static,
        foreign_client: ForeignClient,
        _channel: Channel, // We probably need some config here
        _config: LinkConfig) -> Result<Link, LinkError> {

        // XXX: Validate the inputs

        return Ok(Link {
            foreign_client,
            src_chain: Box::new(src_chain),
            dst_chain: Box::new(dst_chain),
        })
    }

    // Failures
    // * LightClient Failure
    // * FullNode Failures
    // * Verification Failure
    pub fn run(mut self) -> Result<(), LinkError> {
        let subscription = self.src_chain.subscribe(self.dst_chain.id())?;
        for datagrams in subscription.iter() {
            // XXX: We do not get full datagrams here, we get events and they need to be converted
            // to datagrams by performing a series of queries on the chains

            let target_height = 1; // grab from the datagram
            let header = self.src_chain.get_header(target_height);

            verify_proof(&datagrams, &header);

            self.update_client(target_height)?;
            self.dst_chain.submit(datagrams);
        }

        return Ok(())
    }

    // TODO: Move this to ForeignClient to prouce ForeignClientErrors
    fn update_client(&mut self, src_target_height: Height) -> Result<Height, LinkError> {
        return Ok(src_target_height);
        let (src_consensus_state, dst_membership_proof) =
            self.dst_chain.consensus_state(self.src_chain.id(), src_target_height);

        let dst_sh = self.dst_chain.get_header(dst_membership_proof.height + 1);
        // type verifyMembership = (root: CommitmentRoot, proof: CommitmentProof, path: CommitmentPath, value: Value) => boolean (ICS-023)
        if ! verify_consensus_state_inclusion(&src_consensus_state, &dst_membership_proof, &(dst_sh.header.app_hash)) {
            // Error: Destination chain provided invalid consensus_state
            return Err(LinkError::VerificationError())
        }

        // verify client_state on self
        if self.src_chain.get_header(src_consensus_state.height).header == src_consensus_state.signed_header.header {
            return Err(LinkError::HeaderMismatch())
        }

        while src_consensus_state.height < src_target_height {
            let src_signed_headers = self.src_chain.get_minimal_set(src_consensus_state.height, src_target_height);

            // This might fail semantically due to competing relayers
            // Even if this fails, we need to continue
            self.dst_chain.submit(vec![create_client_update_datagram(src_signed_headers)]);

            let (src_consensus_state, dst_membership_proof) = self.dst_chain.consensus_state(self.src_chain.id(), src_target_height);
            let dst_sh = self.dst_chain.get_header(dst_membership_proof.height + 1);
            if ! verify_consensus_state_inclusion(&src_consensus_state, &dst_membership_proof, &(dst_sh.header.app_hash)) {
                // Error: Destination chain provided invalid client_state
                return Err(LinkError::VerificationError())
            }

            if self.src_chain.get_header(src_consensus_state.height).header == src_consensus_state.signed_header.header {
                // Error: consesus_state isn't verified by self light client
                return  Err(LinkError::HeaderMismatch())
            }
        }

        return Ok(src_target_height)
    }
}

// XXX: Give this better naming
fn verify_proof(_datagrams: &Vec<Datagram>, _header: &SignedHeader) {
}

fn verify_consensus_state_inclusion(_consensus_state: &ConsensusState, _membership_proof: &MembershipProof, _hash: &Hash) -> bool {
    return true
}

fn create_client_update_datagram(_header: Vec<SignedHeader>) -> Datagram  {
    return Datagram::NoOp()
}
