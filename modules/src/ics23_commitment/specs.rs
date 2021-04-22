use ics23::ProofSpec;

use ibc_proto::ics23::ProofSpec as ProtoProofSpec;

/// An array of proof specifications.
///
/// This type encapsulates different types of proof specifications, mostly predefined, e.g., for
/// Cosmos-SDK.
/// Additionally, this type also aids in the conversion from `ProofSpec` types from crate `ics23`
/// into proof specifications as represented in the `ibc_proto` type; see the
/// `From` trait(s) below.
pub struct ProofSpecs {
    specs: Vec<ProofSpec>,
}

impl ProofSpecs {
    /// Returns the specification for Cosmos-SDK proofs
    pub fn cosmos() -> Self {
        Self {
            specs: vec![
                ics23::iavl_spec(),       // Format of proofs-iavl (iavl merkle proofs)
                ics23::tendermint_spec(), // Format of proofs-tendermint (crypto/ merkle SimpleProof)
            ],
        }
    }
}

/// Converts from the domain-type (which is represented as an array of `ics23::ProofSpec` from
/// crate `ics23`) to the corresponding proto type.
impl From<ProofSpecs> for Vec<ProtoProofSpec> {
    fn from(domain_specs: ProofSpecs) -> Self {
        let mut raw_specs = vec![];
        for ds in domain_specs.specs.iter() {
            // Convert by encoding, then decoding into the destination type.
            let mut b = Vec::new();
            prost::Message::encode(ds, &mut b).unwrap(); // TODO(Adi): Fix unwraps.
            let c: ProtoProofSpec = prost::Message::decode(&*b).unwrap();
            raw_specs.push(c);
        }
        raw_specs
    }
}
