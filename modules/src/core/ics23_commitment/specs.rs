use crate::prelude::*;
use ibc_proto::ics23::ProofSpec as ProtoProofSpec;
use ics23::ProofSpec;
use serde::{Deserialize, Serialize};

/// An array of proof specifications.
///
/// This type encapsulates different types of proof specifications, mostly predefined, e.g., for
/// Cosmos-SDK.
/// Additionally, this type also aids in the conversion from `ProofSpec` types from crate `ics23`
/// into proof specifications as represented in the `ibc_proto` type; see the
/// `From` trait(s) below.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub struct ProofSpecs(Vec<ProtoProofSpec>);

impl ProofSpecs {
    /// Returns the specification for Cosmos-SDK proofs
    pub fn cosmos() -> Self {
        vec![
            ics23::iavl_spec(),       // Format of proofs-iavl (iavl merkle proofs)
            ics23::tendermint_spec(), // Format of proofs-tendermint (crypto/ merkle SimpleProof)
        ]
        .into()
    }
}

impl Default for ProofSpecs {
    fn default() -> Self {
        Self::cosmos()
    }
}

/// Converts from the domain type (which is represented as a vector of `ics23::ProofSpec`
/// to the corresponding proto type (vector of `ibc_proto::ProofSpec`).
/// TODO: fix with <https://github.com/informalsystems/ibc-rs/issues/853>
impl From<ProofSpecs> for Vec<ProtoProofSpec> {
    fn from(domain_specs: ProofSpecs) -> Self {
        let mut raw_specs = Vec::new();
        for ds in domain_specs.0.iter() {
            // Both `ProofSpec` types implement trait `prost::Message`. Convert by encoding, then
            // decoding into the destination type.
            // Safety note: the source and target data structures are identical, hence the
            // encode/decode conversion here should be infallible.
            let mut encoded = Vec::new();
            prost::Message::encode(ds, &mut encoded).unwrap();
            let decoded: ProtoProofSpec = prost::Message::decode(&*encoded).unwrap();
            raw_specs.push(decoded);
        }
        raw_specs
    }
}

impl From<Vec<ProofSpec>> for ProofSpecs {
    fn from(proto_specs: Vec<ProofSpec>) -> Self {
        let mut specs = Vec::new();
        for ds in proto_specs {
            // Both `ProofSpec` types implement trait `prost::Message`. Convert by encoding, then
            // decoding into the destination type.
            // Safety note: the source and target data structures are identical, hence the
            // encode/decode conversion here should be infallible.
            let mut encoded = Vec::new();
            prost::Message::encode(&ds, &mut encoded).unwrap();
            let decoded: ProtoProofSpec = prost::Message::decode(&*encoded).unwrap();
            specs.push(decoded);
        }
        Self(specs)
    }
}

impl From<Vec<ProtoProofSpec>> for ProofSpecs {
    fn from(specs: Vec<ProtoProofSpec>) -> Self {
        Self(specs)
    }
}
