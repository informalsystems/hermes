/// PublicKey specifies a public key
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct PublicKey {
    /// sum specifies which type of public key is wrapped
    #[prost(oneof="public_key::Sum", tags="1, 2, 3, 4, 5, 15")]
    pub sum: ::std::option::Option<public_key::Sum>,
}
pub mod public_key {
    /// sum specifies which type of public key is wrapped
    #[derive(Clone, PartialEq, ::prost::Oneof)]
    pub enum Sum {
        #[prost(bytes, tag="1")]
        Secp256k1(std::vec::Vec<u8>),
        #[prost(bytes, tag="2")]
        Ed25519(std::vec::Vec<u8>),
        #[prost(bytes, tag="3")]
        Sr25519(std::vec::Vec<u8>),
        #[prost(message, tag="4")]
        Multisig(super::PubKeyMultisigThreshold),
        #[prost(bytes, tag="5")]
        Secp256r1(std::vec::Vec<u8>),
        /// any_pubkey can be used for any pubkey that an app may use which is
        /// not explicitly defined in the oneof
        ///
        /// 15 is largest field that occupies one byte
        #[prost(message, tag="15")]
        AnyPubkey(::prost_types::Any),
    }
}
/// PubKeyMultisigThreshold specifies a public key type which nests multiple public
/// keys and a threshold
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct PubKeyMultisigThreshold {
    #[prost(uint32, tag="1")]
    pub threshold: u32,
    #[prost(message, repeated, tag="2")]
    pub public_keys: ::std::vec::Vec<PublicKey>,
}
/// MultiSignature wraps the signatures from a PubKeyMultisigThreshold.
/// See cosmos.tx.v1betata1.ModeInfo.Multi for how to specify which signers signed and
/// with which modes.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MultiSignature {
    #[prost(bytes, repeated, tag="1")]
    pub signatures: ::std::vec::Vec<std::vec::Vec<u8>>,
}
/// CompactBitArray is an implementation of a space efficient bit array.
/// This is used to ensure that the encoded data takes up a minimal amount of
/// space after proto encoding.
/// This is not thread safe, and is not intended for concurrent usage.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct CompactBitArray {
    #[prost(uint32, tag="1")]
    pub extra_bits_stored: u32,
    #[prost(bytes, tag="2")]
    pub elems: std::vec::Vec<u8>,
}
