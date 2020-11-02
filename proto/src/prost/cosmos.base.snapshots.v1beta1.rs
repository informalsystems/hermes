/// Snapshot contains Tendermint state sync snapshot info.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Snapshot {
    #[prost(uint64, tag="1")]
    pub height: u64,
    #[prost(uint32, tag="2")]
    pub format: u32,
    #[prost(uint32, tag="3")]
    pub chunks: u32,
    #[prost(bytes, tag="4")]
    pub hash: std::vec::Vec<u8>,
    #[prost(message, optional, tag="5")]
    pub metadata: ::std::option::Option<Metadata>,
}
/// Metadata contains SDK-specific snapshot metadata.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Metadata {
    /// SHA-256 chunk hashes
    #[prost(bytes, repeated, tag="1")]
    pub chunk_hashes: ::std::vec::Vec<std::vec::Vec<u8>>,
}
