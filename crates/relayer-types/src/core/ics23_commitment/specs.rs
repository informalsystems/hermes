use ics23::ProofSpec;
use serde::{Deserialize, Serialize};

/// An array of proof specifications.
///
/// This type encapsulates different types of proof specifications, mostly predefined, e.g., for
/// Cosmos-SDK.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct ProofSpecs(Vec<ProofSpec>);

impl ProofSpecs {
    /// Returns the specification for Cosmos-SDK proofs
    pub fn cosmos() -> Self {
        Self(vec![
            ics23::iavl_spec(),       // Format of proofs-iavl (iavl merkle proofs)
            ics23::tendermint_spec(), // Format of proofs-tendermint (crypto/ merkle SimpleProof)
        ])
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn into_vec(self) -> Vec<ProofSpec> {
        self.0
    }
}

impl From<ProofSpecs> for Vec<ProofSpec> {
    fn from(proof_specs: ProofSpecs) -> Self {
        proof_specs.into_vec()
    }
}

impl From<Vec<ProofSpec>> for ProofSpecs {
    fn from(proof_specs: Vec<ProofSpec>) -> Self {
        Self(proof_specs)
    }
}

impl Default for ProofSpecs {
    fn default() -> Self {
        Self::cosmos()
    }
}
