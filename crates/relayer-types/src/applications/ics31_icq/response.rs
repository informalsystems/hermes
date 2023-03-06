use crate::applications::ics31_icq::error::Error;
use crate::signer::Signer;

use ibc_proto::google::protobuf::Any;
use ibc_proto::stride::interchainquery::v1::MsgSubmitQueryResponse;
use prost::Message;
use std::prelude::v1::*;
use std::vec;
use tendermint::merkle::proof::ProofOps as TendermintProofOps;
use tendermint_proto::crypto::{ProofOp, ProofOps};

pub const TYPE_URL: &str = "/stride.interchainquery.v1.MsgSubmitQueryResponse";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CrossChainQueryResponse {
    pub chain_id: String,
    pub query_id: String,
    pub result: Vec<u8>,
    pub height: i64,
    pub proof: TendermintProofOps,
}

fn into_proof_ops(merkle_proof: TendermintProofOps) -> ProofOps {
    ProofOps {
        ops: merkle_proof
            .ops
            .into_iter()
            .map(|o| ProofOp {
                r#type: o.field_type,
                key: o.key,
                data: o.data,
            })
            .collect(),
    }
}

impl CrossChainQueryResponse {
    pub fn new(
        chain_id: String,
        query_id: String,
        result: Vec<u8>,
        height: i64,
        proof: TendermintProofOps,
    ) -> Self {
        Self {
            chain_id,
            query_id,
            result,
            height,
            proof,
        }
    }

    pub fn try_to_any(&self, signer: Signer) -> Result<Any, Error> {
        let mut encoded = vec![];

        let msg_submit_cross_chain_query_result = MsgSubmitQueryResponse {
            chain_id: self.chain_id.to_string(),
            query_id: self.query_id.to_string(),
            result: self.result.clone(),
            proof_ops: Some(into_proof_ops(self.proof.clone())),
            height: self.height,
            from_address: signer.as_ref().to_string(),
        };

        msg_submit_cross_chain_query_result
            .encode(&mut encoded)
            .map_err(|_| Error::proto_encode())?;

        Ok(Any {
            type_url: TYPE_URL.to_string(),
            value: encoded,
        })
    }
}
