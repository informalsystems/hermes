/// CommitInfo defines commit information used by the multi-store when committing
/// a version/height.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct CommitInfo {
    #[prost(int64, tag="1")]
    pub version: i64,
    #[prost(message, repeated, tag="2")]
    pub store_infos: ::std::vec::Vec<StoreInfo>,
}
/// StoreInfo defines store-specific commit information. It contains a reference
/// between a store name and the commit ID.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct StoreInfo {
    #[prost(string, tag="1")]
    pub name: std::string::String,
    #[prost(message, optional, tag="2")]
    pub commit_id: ::std::option::Option<CommitId>,
}
/// CommitID defines the committment information when a specific store is
/// committed.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct CommitId {
    #[prost(int64, tag="1")]
    pub version: i64,
    #[prost(bytes, tag="2")]
    pub hash: std::vec::Vec<u8>,
}
