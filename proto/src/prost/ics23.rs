///*
///ExistenceProof takes a key and a value and a set of steps to perform on it.
///The result of peforming all these steps will provide a "root hash", which can
///be compared to the value in a header.
///
///Since it is computationally infeasible to produce a hash collission for any of the used
///cryptographic hash functions, if someone can provide a series of operations to transform
///a given key and value into a root hash that matches some trusted root, these key and values
///must be in the referenced merkle tree.
///
///The only possible issue is maliablity in LeafOp, such as providing extra prefix data,
///which should be controlled by a spec. Eg. with lengthOp as NONE,
///prefix = FOO, key = BAR, value = CHOICE
///and
///prefix = F, key = OOBAR, value = CHOICE
///would produce the same value.
///
///With LengthOp this is tricker but not impossible. Which is why the "leafPrefixEqual" field
///in the ProofSpec is valuable to prevent this mutability. And why all trees should
///length-prefix the data before hashing it.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ExistenceProof {
    #[prost(bytes, tag = "1")]
    pub key: std::vec::Vec<u8>,
    #[prost(bytes, tag = "2")]
    pub value: std::vec::Vec<u8>,
    #[prost(message, optional, tag = "3")]
    pub leaf: ::std::option::Option<LeafOp>,
    #[prost(message, repeated, tag = "4")]
    pub path: ::std::vec::Vec<InnerOp>,
}
///
///NonExistenceProof takes a proof of two neighbors, one left of the desired key,
///one right of the desired key. If both proofs are valid AND they are neighbors,
///then there is no valid proof for the given key.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct NonExistenceProof {
    /// TODO: remove this as unnecessary??? we prove a range
    #[prost(bytes, tag = "1")]
    pub key: std::vec::Vec<u8>,
    #[prost(message, optional, tag = "2")]
    pub left: ::std::option::Option<ExistenceProof>,
    #[prost(message, optional, tag = "3")]
    pub right: ::std::option::Option<ExistenceProof>,
}
///
///CommitmentProof is either an ExistenceProof or a NonExistenceProof, or a Batch of such messages
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct CommitmentProof {
    #[prost(oneof = "commitment_proof::Proof", tags = "1, 2, 3, 4")]
    pub proof: ::std::option::Option<commitment_proof::Proof>,
}
pub mod commitment_proof {
    #[derive(Clone, PartialEq, ::prost::Oneof)]
    pub enum Proof {
        #[prost(message, tag = "1")]
        Exist(super::ExistenceProof),
        #[prost(message, tag = "2")]
        Nonexist(super::NonExistenceProof),
        #[prost(message, tag = "3")]
        Batch(super::BatchProof),
        #[prost(message, tag = "4")]
        Compressed(super::CompressedBatchProof),
    }
}
///*
///LeafOp represents the raw key-value data we wish to prove, and
///must be flexible to represent the internal transformation from
///the original key-value pairs into the basis hash, for many existing
///merkle trees.
///
///key and value are passed in. So that the signature of this operation is:
///leafOp(key, value) -> output
///
///To process this, first prehash the keys and values if needed (ANY means no hash in this case):
///hkey = prehashKey(key)
///hvalue = prehashValue(value)
///
///Then combine the bytes, and hash it
///output = hash(prefix || length(hkey) || hkey || length(hvalue) || hvalue)
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct LeafOp {
    #[prost(enumeration = "HashOp", tag = "1")]
    pub hash: i32,
    #[prost(enumeration = "HashOp", tag = "2")]
    pub prehash_key: i32,
    #[prost(enumeration = "HashOp", tag = "3")]
    pub prehash_value: i32,
    #[prost(enumeration = "LengthOp", tag = "4")]
    pub length: i32,
    /// prefix is a fixed bytes that may optionally be included at the beginning to differentiate
    /// a leaf node from an inner node.
    #[prost(bytes, tag = "5")]
    pub prefix: std::vec::Vec<u8>,
}
///*
///InnerOp represents a merkle-proof step that is not a leaf.
///It represents concatenating two children and hashing them to provide the next result.
///
///The result of the previous step is passed in, so the signature of this op is:
///innerOp(child) -> output
///
///The result of applying InnerOp should be:
///output = op.hash(op.prefix || child || op.suffix)
///
///where the || operator is concatenation of binary data,
///and child is the result of hashing all the tree below this step.
///
///Any special data, like prepending child with the length, or prepending the entire operation with
///some value to differentiate from leaf nodes, should be included in prefix and suffix.
///If either of prefix or suffix is empty, we just treat it as an empty string
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct InnerOp {
    #[prost(enumeration = "HashOp", tag = "1")]
    pub hash: i32,
    #[prost(bytes, tag = "2")]
    pub prefix: std::vec::Vec<u8>,
    #[prost(bytes, tag = "3")]
    pub suffix: std::vec::Vec<u8>,
}
///*
///ProofSpec defines what the expected parameters are for a given proof type.
///This can be stored in the client and used to validate any incoming proofs.
///
///verify(ProofSpec, Proof) -> Proof | Error
///
///As demonstrated in tests, if we don't fix the algorithm used to calculate the
///LeafHash for a given tree, there are many possible key-value pairs that can
///generate a given hash (by interpretting the preimage differently).
///We need this for proper security, requires client knows a priori what
///tree format server uses. But not in code, rather a configuration object.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ProofSpec {
    /// any field in the ExistenceProof must be the same as in this spec.
    /// except Prefix, which is just the first bytes of prefix (spec can be longer)
    #[prost(message, optional, tag = "1")]
    pub leaf_spec: ::std::option::Option<LeafOp>,
    #[prost(message, optional, tag = "2")]
    pub inner_spec: ::std::option::Option<InnerSpec>,
    /// max_depth (if > 0) is the maximum number of InnerOps allowed (mainly for fixed-depth tries)
    #[prost(int32, tag = "3")]
    pub max_depth: i32,
    /// min_depth (if > 0) is the minimum number of InnerOps allowed (mainly for fixed-depth tries)
    #[prost(int32, tag = "4")]
    pub min_depth: i32,
}
///
///InnerSpec contains all store-specific structure info to determine if two proofs from a
///given store are neighbors.
///
///This enables:
///
///isLeftMost(spec: InnerSpec, op: InnerOp)
///isRightMost(spec: InnerSpec, op: InnerOp)
///isLeftNeighbor(spec: InnerSpec, left: InnerOp, right: InnerOp)
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct InnerSpec {
    /// Child order is the ordering of the children node, must count from 0
    /// iavl tree is [0, 1] (left then right)
    /// merk is [0, 2, 1] (left, right, here)
    #[prost(int32, repeated, tag = "1")]
    pub child_order: ::std::vec::Vec<i32>,
    #[prost(int32, tag = "2")]
    pub child_size: i32,
    #[prost(int32, tag = "3")]
    pub min_prefix_length: i32,
    #[prost(int32, tag = "4")]
    pub max_prefix_length: i32,
    /// empty child is the prehash image that is used when one child is nil (eg. 20 bytes of 0)
    #[prost(bytes, tag = "5")]
    pub empty_child: std::vec::Vec<u8>,
    /// hash is the algorithm that must be used for each InnerOp
    #[prost(enumeration = "HashOp", tag = "6")]
    pub hash: i32,
}
///
///BatchProof is a group of multiple proof types than can be compressed
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct BatchProof {
    #[prost(message, repeated, tag = "1")]
    pub entries: ::std::vec::Vec<BatchEntry>,
}
/// Use BatchEntry not CommitmentProof, to avoid recursion
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct BatchEntry {
    #[prost(oneof = "batch_entry::Proof", tags = "1, 2")]
    pub proof: ::std::option::Option<batch_entry::Proof>,
}
pub mod batch_entry {
    #[derive(Clone, PartialEq, ::prost::Oneof)]
    pub enum Proof {
        #[prost(message, tag = "1")]
        Exist(super::ExistenceProof),
        #[prost(message, tag = "2")]
        Nonexist(super::NonExistenceProof),
    }
}
//***** all items here are compressed forms ******

#[derive(Clone, PartialEq, ::prost::Message)]
pub struct CompressedBatchProof {
    #[prost(message, repeated, tag = "1")]
    pub entries: ::std::vec::Vec<CompressedBatchEntry>,
    #[prost(message, repeated, tag = "2")]
    pub lookup_inners: ::std::vec::Vec<InnerOp>,
}
/// Use BatchEntry not CommitmentProof, to avoid recursion
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct CompressedBatchEntry {
    #[prost(oneof = "compressed_batch_entry::Proof", tags = "1, 2")]
    pub proof: ::std::option::Option<compressed_batch_entry::Proof>,
}
pub mod compressed_batch_entry {
    #[derive(Clone, PartialEq, ::prost::Oneof)]
    pub enum Proof {
        #[prost(message, tag = "1")]
        Exist(super::CompressedExistenceProof),
        #[prost(message, tag = "2")]
        Nonexist(super::CompressedNonExistenceProof),
    }
}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct CompressedExistenceProof {
    #[prost(bytes, tag = "1")]
    pub key: std::vec::Vec<u8>,
    #[prost(bytes, tag = "2")]
    pub value: std::vec::Vec<u8>,
    #[prost(message, optional, tag = "3")]
    pub leaf: ::std::option::Option<LeafOp>,
    /// these are indexes into the lookup_inners table in CompressedBatchProof
    #[prost(int32, repeated, tag = "4")]
    pub path: ::std::vec::Vec<i32>,
}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct CompressedNonExistenceProof {
    /// TODO: remove this as unnecessary??? we prove a range
    #[prost(bytes, tag = "1")]
    pub key: std::vec::Vec<u8>,
    #[prost(message, optional, tag = "2")]
    pub left: ::std::option::Option<CompressedExistenceProof>,
    #[prost(message, optional, tag = "3")]
    pub right: ::std::option::Option<CompressedExistenceProof>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, ::prost::Enumeration)]
#[repr(i32)]
pub enum HashOp {
    /// NO_HASH is the default if no data passed. Note this is an illegal argument some places.
    NoHash = 0,
    Sha256 = 1,
    Sha512 = 2,
    Keccak = 3,
    Ripemd160 = 4,
    /// ripemd160(sha256(x))
    Bitcoin = 5,
}
///*
///LengthOp defines how to process the key and value of the LeafOp
///to include length information. After encoding the length with the given
///algorithm, the length will be prepended to the key and value bytes.
///(Each one with it's own encoded length)
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, ::prost::Enumeration)]
#[repr(i32)]
pub enum LengthOp {
    /// NO_PREFIX don't include any length info
    NoPrefix = 0,
    /// VAR_PROTO uses protobuf (and go-amino) varint encoding of the length
    VarProto = 1,
    /// VAR_RLP uses rlp int encoding of the length
    VarRlp = 2,
    /// FIXED32_BIG uses big-endian encoding of the length as a 32 bit integer
    Fixed32Big = 3,
    /// FIXED32_LITTLE uses little-endian encoding of the length as a 32 bit integer
    Fixed32Little = 4,
    /// FIXED64_BIG uses big-endian encoding of the length as a 64 bit integer
    Fixed64Big = 5,
    /// FIXED64_LITTLE uses little-endian encoding of the length as a 64 bit integer
    Fixed64Little = 6,
    /// REQUIRE_32_BYTES is like NONE, but will fail if the input is not exactly 32 bytes (sha256 output)
    Require32Bytes = 7,
    /// REQUIRE_64_BYTES is like NONE, but will fail if the input is not exactly 64 bytes (sha512 output)
    Require64Bytes = 8,
}
