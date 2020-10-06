/// TxResponse defines a structure containing relevant tx data and metadata. The
/// tags are stringified and the log is JSON decoded.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct TxResponse {
    /// The block height
    #[prost(int64, tag="1")]
    pub height: i64,
    /// The transaction hash.
    #[prost(string, tag="2")]
    pub txhash: std::string::String,
    /// Namespace for the Code
    #[prost(string, tag="3")]
    pub codespace: std::string::String,
    /// Response code.
    #[prost(uint32, tag="4")]
    pub code: u32,
    /// Result bytes, if any.
    #[prost(string, tag="5")]
    pub data: std::string::String,
    /// The output of the application's logger (raw string). May be
    /// non-deterministic.
    #[prost(string, tag="6")]
    pub raw_log: std::string::String,
    /// The output of the application's logger (typed). May be non-deterministic.
    #[prost(message, repeated, tag="7")]
    pub logs: ::std::vec::Vec<AbciMessageLog>,
    /// Additional information. May be non-deterministic.
    #[prost(string, tag="8")]
    pub info: std::string::String,
    /// Amount of gas requested for transaction.
    #[prost(int64, tag="9")]
    pub gas_wanted: i64,
    /// Amount of gas consumed by transaction.
    #[prost(int64, tag="10")]
    pub gas_used: i64,
    /// The request transaction bytes.
    #[prost(message, optional, tag="11")]
    pub tx: ::std::option::Option<::prost_types::Any>,
    /// Time of the previous block. For heights > 1, it's the weighted median of
    /// the timestamps of the valid votes in the block.LastCommit. For height == 1,
    /// it's genesis time.
    #[prost(string, tag="12")]
    pub timestamp: std::string::String,
}
/// ABCIMessageLog defines a structure containing an indexed tx ABCI message log.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct AbciMessageLog {
    #[prost(uint32, tag="1")]
    pub msg_index: u32,
    #[prost(string, tag="2")]
    pub log: std::string::String,
    /// Events contains a slice of Event objects that were emitted during some
    /// execution.
    #[prost(message, repeated, tag="3")]
    pub events: ::std::vec::Vec<StringEvent>,
}
/// StringEvent defines en Event object wrapper where all the attributes
/// contain key/value pairs that are strings instead of raw bytes.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct StringEvent {
    #[prost(string, tag="1")]
    pub r#type: std::string::String,
    #[prost(message, repeated, tag="2")]
    pub attributes: ::std::vec::Vec<Attribute>,
}
/// Attribute defines an attribute wrapper where the key and value are
/// strings instead of raw bytes.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Attribute {
    #[prost(string, tag="1")]
    pub key: std::string::String,
    #[prost(string, tag="2")]
    pub value: std::string::String,
}
/// GasInfo defines tx execution gas context.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct GasInfo {
    /// GasWanted is the maximum units of work we allow this tx to perform.
    #[prost(uint64, tag="1")]
    pub gas_wanted: u64,
    /// GasUsed is the amount of gas actually consumed.
    #[prost(uint64, tag="2")]
    pub gas_used: u64,
}
/// Result is the union of ResponseFormat and ResponseCheckTx.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Result {
    /// Data is any data returned from message or handler execution. It MUST be
    /// length prefixed in order to separate data from multiple message executions.
    #[prost(bytes, tag="1")]
    pub data: std::vec::Vec<u8>,
    /// Log contains the log information from message or handler execution.
    #[prost(string, tag="2")]
    pub log: std::string::String,
    /// Events contains a slice of Event objects that were emitted during message
    /// or handler execution.
    #[prost(message, repeated, tag="3")]
    pub events: ::std::vec::Vec<super::super::super::super::tendermint::abci::Event>,
}
/// SimulationResponse defines the response generated when a transaction is
/// successfully simulated.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SimulationResponse {
    #[prost(message, optional, tag="1")]
    pub gas_info: ::std::option::Option<GasInfo>,
    #[prost(message, optional, tag="2")]
    pub result: ::std::option::Option<Result>,
}
/// MsgData defines the data returned in a Result object during message
/// execution.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgData {
    #[prost(string, tag="1")]
    pub msg_type: std::string::String,
    #[prost(bytes, tag="2")]
    pub data: std::vec::Vec<u8>,
}
/// TxMsgData defines a list of MsgData. A transaction will have a MsgData object
/// for each message.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct TxMsgData {
    #[prost(message, repeated, tag="1")]
    pub data: ::std::vec::Vec<MsgData>,
}
/// SearchTxsResult defines a structure for querying txs pageable
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SearchTxsResult {
    /// Count of all txs
    #[prost(uint64, tag="1")]
    pub total_count: u64,
    /// Count of txs in current page
    #[prost(uint64, tag="2")]
    pub count: u64,
    /// Index of current page, start from 1
    #[prost(uint64, tag="3")]
    pub page_number: u64,
    /// Count of total pages
    #[prost(uint64, tag="4")]
    pub page_total: u64,
    /// Max count txs per page
    #[prost(uint64, tag="5")]
    pub limit: u64,
    /// List of txs in current page
    #[prost(message, repeated, tag="6")]
    pub txs: ::std::vec::Vec<TxResponse>,
}
