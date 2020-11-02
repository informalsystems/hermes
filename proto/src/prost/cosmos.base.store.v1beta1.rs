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
/// SnapshotItem is an item contained in a rootmulti.Store snapshot.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SnapshotItem {
    /// item is the specific type of snapshot item.
    #[prost(oneof="snapshot_item::Item", tags="1, 2")]
    pub item: ::std::option::Option<snapshot_item::Item>,
}
pub mod snapshot_item {
    /// item is the specific type of snapshot item.
    #[derive(Clone, PartialEq, ::prost::Oneof)]
    pub enum Item {
        #[prost(message, tag="1")]
        Store(super::SnapshotStoreItem),
        #[prost(message, tag="2")]
        Iavl(super::SnapshotIavlItem),
    }
}
/// SnapshotStoreItem contains metadata about a snapshotted store.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SnapshotStoreItem {
    #[prost(string, tag="1")]
    pub name: std::string::String,
}
/// SnapshotIAVLItem is an exported IAVL node.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SnapshotIavlItem {
    #[prost(bytes, tag="1")]
    pub key: std::vec::Vec<u8>,
    #[prost(bytes, tag="2")]
    pub value: std::vec::Vec<u8>,
    #[prost(int64, tag="3")]
    pub version: i64,
    #[prost(int32, tag="4")]
    pub height: i32,
}
