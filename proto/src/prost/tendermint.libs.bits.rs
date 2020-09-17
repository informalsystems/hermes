#[derive(Clone, PartialEq, ::prost::Message)]
pub struct BitArray {
    #[prost(int64, tag="1")]
    pub bits: i64,
    #[prost(uint64, repeated, tag="2")]
    pub elems: ::std::vec::Vec<u64>,
}
