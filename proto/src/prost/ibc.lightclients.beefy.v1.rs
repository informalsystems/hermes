/// ClientState from Tendermint tracks the current validator set, latest height,
/// and a possible frozen height.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ClientState {
    /// Latest mmr root hash
    #[prost(bytes = "vec", tag = "1")]
    pub mmr_root_hash: ::prost::alloc::vec::Vec<u8>,
    /// block number for the latest mmr_root_hash
    #[prost(uint32, tag = "2")]
    pub latest_beefy_height: u32,
    /// Block height when the client was frozen due to a misbehaviour
    #[prost(uint64, tag = "3")]
    pub frozen_height: u64,
    /// block number that the beefy protocol was activated on the relay chain.
    /// This shoould be the first block in the merkle-mountain-range tree.
    #[prost(uint32, tag = "4")]
    pub beefy_activation_block: u32,
    /// authorities for the current round
    #[prost(message, optional, tag = "5")]
    pub authority: ::core::option::Option<BeefyAuthoritySet>,
    /// authorities for the next round
    #[prost(message, optional, tag = "6")]
    pub next_authority_set: ::core::option::Option<BeefyAuthoritySet>,
}
/// Actual payload items
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct PayloadItem {
    /// 2-byte payload id
    #[prost(bytes = "vec", tag = "1")]
    pub payload_id: ::prost::alloc::vec::Vec<u8>,
    /// arbitrary length payload data., eg mmr_root_hash
    #[prost(bytes = "vec", tag = "2")]
    pub payload_data: ::prost::alloc::vec::Vec<u8>,
}
/// Commitment message signed by beefy validators
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Commitment {
    /// array of payload items signed by Beefy validators
    #[prost(message, repeated, tag = "1")]
    pub payload: ::prost::alloc::vec::Vec<PayloadItem>,
    /// block number for this commitment
    #[prost(uint32, tag = "2")]
    pub block_numer: u32,
    /// validator set that signed this commitment
    #[prost(uint64, tag = "3")]
    pub validator_set_id: u64,
}
/// Signature belonging to a single validator
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct CommitmentSignature {
    /// actual signature bytes
    #[prost(bytes = "vec", tag = "1")]
    pub signature: ::prost::alloc::vec::Vec<u8>,
    /// authority leaf index in the merkle tree.
    #[prost(uint32, tag = "2")]
    pub authority_index: u32,
}
/// signed commitment data
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SignedCommitment {
    /// commitment data being signed
    #[prost(message, optional, tag = "1")]
    pub commitment: ::core::option::Option<Commitment>,
    /// gotten from rpc subscription
    #[prost(message, repeated, tag = "2")]
    pub signatures: ::prost::alloc::vec::Vec<CommitmentSignature>,
}
/// data needed to update the client
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MmrUpdateProof {
    /// the new mmr leaf SCALE encoded.
    #[prost(message, optional, tag = "1")]
    pub mmr_leaf: ::core::option::Option<BeefyMmrLeaf>,
    /// leaf index for the mmr_leaf
    #[prost(uint64, tag = "2")]
    pub mmr_leaf_index: u64,
    /// proof that this mmr_leaf index is valid.
    #[prost(bytes = "vec", repeated, tag = "3")]
    pub mmr_proof: ::prost::alloc::vec::Vec<::prost::alloc::vec::Vec<u8>>,
    /// signed commitment data
    #[prost(message, optional, tag = "4")]
    pub signed_commitment: ::core::option::Option<SignedCommitment>,
    /// generated using full authority list from runtime
    #[prost(bytes = "vec", repeated, tag = "5")]
    pub authorities_proof: ::prost::alloc::vec::Vec<::prost::alloc::vec::Vec<u8>>,
}
/// ConsensusState defines the consensus state from Tendermint.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ConsensusState {
    /// timestamp that corresponds to the block height in which the ConsensusState
    /// was stored.
    #[prost(message, optional, tag = "1")]
    pub timestamp: ::core::option::Option<super::super::super::super::google::protobuf::Timestamp>,
    /// packet commitment root
    #[prost(bytes = "vec", tag = "2")]
    pub root: ::prost::alloc::vec::Vec<u8>,
    /// proof of inclusion for this parachain header in the Mmr.
    #[prost(message, optional, tag = "4")]
    pub parachain_header: ::core::option::Option<ParachainHeader>,
}
/// Misbehaviour is a wrapper over two conflicting Headers
/// that implements Misbehaviour interface expected by ICS-02
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Misbehaviour {
    #[prost(message, optional, tag = "2")]
    pub header_1: ::core::option::Option<Header>,
    #[prost(message, optional, tag = "3")]
    pub header_2: ::core::option::Option<Header>,
}
/// Header contains the neccessary data to proove finality about IBC commitments
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Header {
    /// parachain headers needed for proofs and ConsensusState
    #[prost(message, repeated, tag = "1")]
    pub parachain_headers: ::prost::alloc::vec::Vec<ParachainHeader>,
    /// mmr proofs for the headers gotten from rpc "mmr_generateProofs"
    #[prost(bytes = "vec", repeated, tag = "2")]
    pub mmr_proofs: ::prost::alloc::vec::Vec<::prost::alloc::vec::Vec<u8>>,
    /// size of the mmr for the given proof
    #[prost(uint64, tag = "3")]
    pub mmr_size: u64,
    /// optional payload to update the mmr root hash.
    #[prost(message, optional, tag = "4")]
    pub mmr_update_proof: ::core::option::Option<MmrUpdateProof>,
}
/// data needed to prove parachain header inclusion in mmr.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ParachainHeader {
    /// scale-encoded parachain header bytes
    #[prost(bytes = "vec", tag = "1")]
    pub parachain_header: ::prost::alloc::vec::Vec<u8>,
    /// reconstructed MmrLeaf, see beefy-go spec
    #[prost(message, optional, tag = "2")]
    pub mmr_leaf_partial: ::core::option::Option<BeefyMmrLeafPartial>,
    /// para_id of the header.
    #[prost(uint32, tag = "3")]
    pub para_id: u32,
    /// proofs for our header in the parachain heads root
    #[prost(bytes = "vec", repeated, tag = "4")]
    pub parachain_heads_proof: ::prost::alloc::vec::Vec<::prost::alloc::vec::Vec<u8>>,
    /// leaf index for parachain heads proof
    #[prost(uint32, tag = "5")]
    pub heads_leaf_index: u32,
    /// total number of para heads in parachain_heads_root
    #[prost(uint32, tag = "6")]
    pub heads_total_count: u32,
    /// trie merkle proof of inclusion in header.extrinsic_root
    /// this already encodes the actual extrinsic
    #[prost(bytes = "vec", repeated, tag = "7")]
    pub extrinsic_proof: ::prost::alloc::vec::Vec<::prost::alloc::vec::Vec<u8>>,
}
/// Partial data for MmrLeaf
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct BeefyMmrLeafPartial {
    /// leaf version
    #[prost(uint32, tag = "1")]
    pub version: u32,
    /// parent block for this leaf
    #[prost(uint32, tag = "2")]
    pub parent_number: u32,
    /// parent hash for this leaf
    #[prost(bytes = "vec", tag = "3")]
    pub parent_hash: ::prost::alloc::vec::Vec<u8>,
    /// next authority set.
    #[prost(message, optional, tag = "4")]
    pub beefy_next_authority_set: ::core::option::Option<BeefyAuthoritySet>,
}
/// Beefy Authority Info
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct BeefyAuthoritySet {
    /// Id of the authority set, it should be strictly increasing
    #[prost(uint64, tag = "1")]
    pub id: u64,
    /// size of the authority set
    #[prost(uint32, tag = "2")]
    pub len: u32,
    /// merkle root of the sorted authority public keys.
    #[prost(bytes = "vec", tag = "3")]
    pub authority_root: ::prost::alloc::vec::Vec<u8>,
}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct BeefyMmrLeaf {
    /// leaf version
    #[prost(uint32, tag = "1")]
    pub version: u32,
    /// parent block for this leaf
    #[prost(uint32, tag = "2")]
    pub parent_number: u32,
    /// parent hash for this leaf
    #[prost(bytes = "vec", tag = "3")]
    pub parent_hash: ::prost::alloc::vec::Vec<u8>,
    /// beefy next authority set.
    #[prost(message, optional, tag = "4")]
    pub beefy_next_authority_set: ::core::option::Option<BeefyAuthoritySet>,
    /// merkle root hash of parachain heads included in the leaf.
    #[prost(bytes = "vec", tag = "5")]
    pub parachain_heads: ::prost::alloc::vec::Vec<u8>,
}
