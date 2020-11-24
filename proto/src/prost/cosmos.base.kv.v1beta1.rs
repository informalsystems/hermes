/// Pairs defines a repeated slice of Pair objects.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Pairs {
    #[prost(message, repeated, tag = "1")]
    pub pairs: ::std::vec::Vec<Pair>,
}
/// Pair defines a key/value bytes tuple.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Pair {
    #[prost(bytes, tag = "1")]
    pub key: std::vec::Vec<u8>,
    #[prost(bytes, tag = "2")]
    pub value: std::vec::Vec<u8>,
}
