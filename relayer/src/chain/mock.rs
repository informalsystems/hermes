#![allow(dead_code, unused_variables)]

use prost_types::Any;
use tendermint::account::Id;
use tendermint_testgen::light_block::TMLightBlock;

use ibc::ics07_tendermint::client_state::ClientState as TendermintClientState;
use ibc::ics07_tendermint::consensus_state::ConsensusState as TendermintConsensusState;
use ibc::ics07_tendermint::header::Header as TendermintHeader;
use ibc::ics18_relayer::context::ICS18Context;
use ibc::ics23_commitment::merkle::MerkleProof;
use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc::ics24_host::Path;
use ibc::mock::context::MockContext;
use ibc::mock::host::HostType;
use ibc::Height;

use crate::chain::{Chain, QueryResponse};
use crate::error::Error;
use crate::keyring::store::{KeyEntry, KeyRing};
use ibc::ics23_commitment::commitment::CommitmentPrefix;

/// The representation of a mocked chain as the relayer sees it.
/// The relayer runtime and the light client will engage with the MockChain to query/send tx.
pub struct MockChain {
    pub context: MockContext,
}

impl MockChain {
    pub fn new() -> MockChain {
        let chain_version = 1;
        MockChain {
            context: MockContext::new(
                ChainId::new("mockgaia".to_string(), chain_version),
                HostType::SyntheticTendermint,
                50,
                Height::new(chain_version, 20),
            ),
        }
    }
}

impl Chain for MockChain {
    type LightBlock = TMLightBlock;
    type Header = TendermintHeader;
    type ConsensusState = TendermintConsensusState;
    type ClientState = TendermintClientState;

    fn id(&self) -> &ChainId {
        unimplemented!()
    }

    fn keybase(&self) -> &KeyRing {
        unimplemented!()
    }

    fn query(&self, data: Path, height: Height, prove: bool) -> Result<QueryResponse, Error> {
        unimplemented!()
    }

    fn send_tx(&self, proto_msgs: Vec<Any>) -> Result<String, Error> {
        unimplemented!()
    }

    fn get_signer(&mut self) -> Result<Id, Error> {
        unimplemented!()
    }

    fn get_key(&mut self) -> Result<KeyEntry, Error> {
        unimplemented!()
    }

    fn build_client_state(&self, height: Height) -> Result<Self::ClientState, Error> {
        unimplemented!()
    }

    fn build_consensus_state(
        &self,
        light_block: Self::LightBlock,
    ) -> Result<Self::ConsensusState, Error> {
        unimplemented!()
    }

    fn build_header(
        &self,
        trusted_light_block: Self::LightBlock,
        target_light_block: Self::LightBlock,
    ) -> Result<Self::Header, Error> {
        unimplemented!()
    }

    fn query_latest_height(&self) -> Result<Height, Error> {
        Ok(self.context.query_latest_height())
    }

    fn query_client_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<Self::ClientState, Error> {
        unimplemented!()
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        unimplemented!()
    }

    fn proven_client_state(
        &self,
        client_id: &ClientId,
        height: Height,
    ) -> Result<(Self::ClientState, MerkleProof), Error> {
        unimplemented!()
    }

    fn proven_client_consensus(
        &self,
        client_id: &ClientId,
        consensus_height: Height,
        height: Height,
    ) -> Result<(Self::ConsensusState, MerkleProof), Error> {
        unimplemented!()
    }
}

// Integration tests with the modules
mod test {}
