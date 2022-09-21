/// MerkleRoot defines a merkle root hash.
/// In the Cosmos SDK, the AppHash of a block header becomes the root.
#[derive(::serde::Serialize, ::serde::Deserialize)]
#[cfg_attr(feature = "json-schema", derive(::schemars::JsonSchema))]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MerkleRoot {
    #[prost(bytes="vec", tag="1")]
    #[serde(with = "crate::base64")]
    #[cfg_attr(feature = "json-schema", schemars(with = "String"))]
    pub hash: ::prost::alloc::vec::Vec<u8>,
}
/// MerklePrefix is merkle path prefixed to the key.
/// The constructed key from the Path and the key will be append(Path.KeyPath,
/// append(Path.KeyPrefix, key...))
#[derive(::serde::Serialize, ::serde::Deserialize)]
#[cfg_attr(feature = "json-schema", derive(::schemars::JsonSchema))]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MerklePrefix {
    #[prost(bytes="vec", tag="1")]
    #[serde(with = "crate::base64")]
    #[cfg_attr(feature = "json-schema", schemars(with = "String"))]
    pub key_prefix: ::prost::alloc::vec::Vec<u8>,
}
/// MerklePath is the path used to verify commitment proofs, which can be an
/// arbitrary structured object (defined by a commitment type).
/// MerklePath is represented from root-to-leaf
#[derive(::serde::Serialize, ::serde::Deserialize)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MerklePath {
    #[prost(string, repeated, tag="1")]
    pub key_path: ::prost::alloc::vec::Vec<::prost::alloc::string::String>,
}
/// MerkleProof is a wrapper type over a chain of CommitmentProofs.
/// It demonstrates membership or non-membership for an element or set of
/// elements, verifiable in conjunction with a known commitment root. Proofs
/// should be succinct.
/// MerkleProofs are ordered from leaf-to-root
#[derive(::serde::Serialize, ::serde::Deserialize)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MerkleProof {
    #[prost(message, repeated, tag="1")]
    pub proofs: ::prost::alloc::vec::Vec<super::super::super::super::ics23::CommitmentProof>,
}
