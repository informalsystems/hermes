use crate::signer::Signer;

use crate::applications::ics31_icq::proto::MsgSubmitQueryResponse;
use ibc_proto::google::protobuf::Any;
use std::prelude::v1::*;
use std::vec;
use tendermint::merkle::proof::ProofOps as TendermintProofOps;
use tendermint_proto::crypto::{ProofOp, ProofOps};

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

    pub fn to_any(&self, signer: Signer, type_url: &str) -> Any {
        let mut encoded = vec![];

        let msg_submit_cross_chain_query_result = MsgSubmitQueryResponse {
            chain_id: self.chain_id.to_string(),
            query_id: self.query_id.to_string(),
            result: self.result.clone(),
            proof_ops: Some(into_proof_ops(self.proof.clone())),
            height: self.height,
            from_address: signer.as_ref().to_string(),
        };

        prost::Message::encode(&msg_submit_cross_chain_query_result, &mut encoded).unwrap();
        Any {
            type_url: type_url.to_string(),
            value: encoded,
        }
    }
}
