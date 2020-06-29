use tendermint_rpc::endpoint::abci_query::AbciQuery;

use tendermint::abci;

use crate::ics23_commitment::{CommitmentPath, CommitmentProof};

use crate::error;
use crate::ics04_channel::channel::ChannelEnd;
use crate::ics24_host::identifier::{ChannelId, PortId};
use crate::path::{ChannelEndsPath, Path};
use crate::query::{IbcQuery, IbcResponse};
use crate::Height;

pub struct QueryChannel {
    pub chain_height: Height,
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub channel_ends_path: ChannelEndsPath,
    pub prove: bool,
}

impl QueryChannel {
    pub fn new(chain_height: Height, port_id: PortId, channel_id: ChannelId, prove: bool) -> Self {
        Self {
            chain_height,
            port_id: port_id.clone(),
            channel_id: channel_id.clone(),
            channel_ends_path: ChannelEndsPath::new(port_id, channel_id),
            prove,
        }
    }
}

impl IbcQuery for QueryChannel {
    type Response = ChannelResponse;

    fn path(&self) -> abci::Path {
        "/store/ibc/key".parse().unwrap()
    }

    fn height(&self) -> Height {
        self.chain_height
    }

    fn prove(&self) -> bool {
        self.prove
    }

    fn data(&self) -> Vec<u8> {
        self.channel_ends_path.to_key().into()
    }
}

pub struct ChannelResponse {
    pub channel: ChannelEnd,
    pub proof: Option<CommitmentProof>,
    pub proof_path: CommitmentPath,
    pub proof_height: Height,
}

impl ChannelResponse {
    pub fn new(
        port_id: PortId,
        channel_id: ChannelId,
        channel: ChannelEnd,
        abci_proof: Option<CommitmentProof>,
        proof_height: Height,
    ) -> Self {
        let proof_path = CommitmentPath::from_path(ChannelEndsPath::new(port_id, channel_id));

        ChannelResponse {
            channel,
            proof: abci_proof,
            proof_path,
            proof_height,
        }
    }
}

impl IbcResponse<QueryChannel> for ChannelResponse {
    fn from_abci_response(query: QueryChannel, response: AbciQuery) -> Result<Self, error::Error> {
        Ok(ChannelResponse::new(
            query.port_id,
            query.channel_id,
            amino_unmarshal_binary_length_prefixed(&response.value)?,
            response.proof,
            response.height.into(),
        ))
    }
}

fn amino_unmarshal_binary_length_prefixed<T>(_bytes: &[u8]) -> Result<T, error::Error> {
    todo!()
}
