use crate::prelude::*;
use ibc_proto::ics23::{InnerSpec as IbcInnerSpec, LeafOp as IbcLeafOp, ProofSpec as IbcProofSpec};
use ics23::{InnerSpec as Ics23InnerSpec, LeafOp as Ics23LeafOp, ProofSpec as Ics23ProofSpec};
use serde::{Deserialize, Serialize};

/// An array of proof specifications.
///
/// This type encapsulates different types of proof specifications, mostly predefined, e.g., for
/// Cosmos-SDK.
/// Additionally, this type also aids in the conversion from `ProofSpec` types from crate `ics23`
/// into proof specifications as represented in the `ibc_proto` type; see the
/// `From` trait(s) below.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub struct ProofSpecs(Vec<ProofSpec>);

impl ProofSpecs {
    /// Returns the specification for Cosmos-SDK proofs
    pub fn cosmos() -> Self {
        vec![
            ics23::iavl_spec(),       // Format of proofs-iavl (iavl merkle proofs)
            ics23::tendermint_spec(), // Format of proofs-tendermint (crypto/ merkle SimpleProof)
        ]
        .into()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl Default for ProofSpecs {
    fn default() -> Self {
        Self::cosmos()
    }
}

impl From<Vec<IbcProofSpec>> for ProofSpecs {
    fn from(ibc_specs: Vec<IbcProofSpec>) -> Self {
        Self(ibc_specs.into_iter().map(ProofSpec).collect())
    }
}

impl From<Vec<Ics23ProofSpec>> for ProofSpecs {
    fn from(ics23_specs: Vec<Ics23ProofSpec>) -> Self {
        Self(
            ics23_specs
                .into_iter()
                .map(|ics23_spec| ics23_spec.into())
                .collect(),
        )
    }
}

impl From<ProofSpecs> for Vec<Ics23ProofSpec> {
    fn from(specs: ProofSpecs) -> Self {
        specs.0.into_iter().map(|spec| spec.into()).collect()
    }
}

impl From<ProofSpecs> for Vec<IbcProofSpec> {
    fn from(specs: ProofSpecs) -> Self {
        specs.0.into_iter().map(|spec| spec.0).collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
struct ProofSpec(IbcProofSpec);

impl From<Ics23ProofSpec> for ProofSpec {
    fn from(spec: Ics23ProofSpec) -> Self {
        Self(IbcProofSpec {
            leaf_spec: spec.leaf_spec.map(|lop| LeafOp::from(lop).0),
            inner_spec: spec.inner_spec.map(|ispec| InnerSpec::from(ispec).0),
            max_depth: spec.max_depth,
            min_depth: spec.min_depth,
        })
    }
}

impl From<ProofSpec> for Ics23ProofSpec {
    fn from(spec: ProofSpec) -> Self {
        let spec = spec.0;
        Ics23ProofSpec {
            leaf_spec: spec.leaf_spec.map(|lop| LeafOp(lop).into()),
            inner_spec: spec.inner_spec.map(|ispec| InnerSpec(ispec).into()),
            max_depth: spec.max_depth,
            min_depth: spec.min_depth,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
struct LeafOp(IbcLeafOp);

impl From<Ics23LeafOp> for LeafOp {
    fn from(leaf_op: Ics23LeafOp) -> Self {
        Self(IbcLeafOp {
            hash: leaf_op.hash,
            prehash_key: leaf_op.prehash_key,
            prehash_value: leaf_op.prehash_value,
            length: leaf_op.length,
            prefix: leaf_op.prefix,
        })
    }
}

impl From<LeafOp> for Ics23LeafOp {
    fn from(leaf_op: LeafOp) -> Self {
        let leaf_op = leaf_op.0;
        Ics23LeafOp {
            hash: leaf_op.hash,
            prehash_key: leaf_op.prehash_key,
            prehash_value: leaf_op.prehash_value,
            length: leaf_op.length,
            prefix: leaf_op.prefix,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
struct InnerSpec(IbcInnerSpec);

impl From<Ics23InnerSpec> for InnerSpec {
    fn from(inner_spec: Ics23InnerSpec) -> Self {
        Self(IbcInnerSpec {
            child_order: inner_spec.child_order,
            child_size: inner_spec.child_size,
            min_prefix_length: inner_spec.min_prefix_length,
            max_prefix_length: inner_spec.max_prefix_length,
            empty_child: inner_spec.empty_child,
            hash: inner_spec.hash,
        })
    }
}

impl From<InnerSpec> for Ics23InnerSpec {
    fn from(inner_spec: InnerSpec) -> Self {
        let inner_spec = inner_spec.0;
        Ics23InnerSpec {
            child_order: inner_spec.child_order,
            child_size: inner_spec.child_size,
            min_prefix_length: inner_spec.min_prefix_length,
            max_prefix_length: inner_spec.max_prefix_length,
            empty_child: inner_spec.empty_child,
            hash: inner_spec.hash,
        }
    }
}
