use crate::ics23_commitment::commitment::CommitmentPrefix;

use ibc_proto::ibc::core::commitment::v1::MerklePath;

pub fn apply_prefix(
    prefix: &CommitmentPrefix,
    _path: String,
) -> Result<MerklePath, Box<dyn std::error::Error>> {
    if prefix.is_empty() {
        return Err("empty prefix".into());
    }

    // TODO
    Ok(MerklePath { key_path: None })
}

// TODO - get this from the ics23 crate proof
pub fn cosmos_specs() -> Vec<ibc_proto::ics23::ProofSpec> {
    vec![
        // Format of proofs-iavl (iavl merkle proofs)
        ibc_proto::ics23::ProofSpec {
            leaf_spec: Some(ibc_proto::ics23::LeafOp {
                hash: 1,
                prehash_key: 0,
                prehash_value: 1,
                length: 1,
                prefix: vec![],
            }),
            inner_spec: Some(ibc_proto::ics23::InnerSpec {
                child_order: vec![0, 1],
                child_size: 33,
                min_prefix_length: 4,
                max_prefix_length: 12,
                empty_child: vec![],
                hash: 1,
            }),
            max_depth: 0,
            min_depth: 0,
        },
        // Format of proofs-tendermint (crypto/ merkle SimpleProof)
        ibc_proto::ics23::ProofSpec {
            leaf_spec: Some(ibc_proto::ics23::LeafOp {
                hash: 1,
                prehash_key: 0,
                prehash_value: 1,
                length: 1,
                prefix: vec![],
            }),
            inner_spec: Some(ibc_proto::ics23::InnerSpec {
                child_order: vec![0, 1],
                child_size: 32,
                min_prefix_length: 1,
                max_prefix_length: 1,
                empty_child: vec![],
                hash: 1,
            }),
            max_depth: 0,
            min_depth: 0,
        },
    ]
}
