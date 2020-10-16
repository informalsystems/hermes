/// MerkleRoot defines a merkle root hash.
/// In the Cosmos SDK, the AppHash of a block header becomes the root.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MerkleRoot {
    #[prost(bytes, tag="1")]
    pub hash: std::vec::Vec<u8>,
}
/// MerklePrefix is merkle path prefixed to the key.
/// The constructed key from the Path and the key will be append(Path.KeyPath,
/// append(Path.KeyPrefix, key...))
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MerklePrefix {
    #[prost(bytes, tag="1")]
    pub key_prefix: std::vec::Vec<u8>,
}
/// MerklePath is the path used to verify commitment proofs, which can be an
/// arbitrary structured object (defined by a commitment type).
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MerklePath {
    #[prost(message, optional, tag="1")]
    pub key_path: ::std::option::Option<KeyPath>,
}
/// MerkleProof is a wrapper type that contains a merkle proof.
/// It demonstrates membership or non-membership for an element or set of
/// elements, verifiable in conjunction with a known commitment root. Proofs
/// should be succinct.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MerkleProof {
    #[prost(message, optional, tag="1")]
    pub proof: ::std::option::Option<::tendermint_proto::crypto::ProofOps>,
}
/// KeyPath defines a slice of keys
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct KeyPath {
    #[prost(message, repeated, tag="1")]
    pub keys: ::std::vec::Vec<Key>,
}
/// Key defines a proof Key
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Key {
    #[prost(bytes, tag="1")]
    pub name: std::vec::Vec<u8>,
    #[prost(enumeration="KeyEncoding", tag="2")]
    pub enc: i32,
}
/// KeyEncoding defines the encoding format of a key's bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, ::prost::Enumeration)]
#[repr(i32)]
pub enum KeyEncoding {
    /// URL encoding
    UrlUnspecified = 0,
    /// Hex encoding
    Hex = 1,
}
