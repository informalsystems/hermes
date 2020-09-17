/// SignatureDescriptors wraps multiple SignatureDescriptor's.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SignatureDescriptors {
    /// signatures are the signature descriptors
    #[prost(message, repeated, tag="1")]
    pub signatures: ::std::vec::Vec<SignatureDescriptor>,
}
/// SignatureDescriptor is a convenience type which represents the full data for a
/// signature including the public key of the signer, signing modes and the signature
/// itself. It is primarily used for coordinating signatures between clients.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SignatureDescriptor {
    /// public_key is the public key of the signer
    #[prost(message, optional, tag="1")]
    pub public_key: ::std::option::Option<super::super::super::base::crypto::v1beta1::PublicKey>,
    #[prost(message, optional, tag="2")]
    pub data: ::std::option::Option<signature_descriptor::Data>,
    /// sequence is the sequence of the account, which describes the
    /// number of committed transactions signed by a given address. It is used to prevent
    /// replay attacks.
    #[prost(uint64, tag="3")]
    pub sequence: u64,
}
pub mod signature_descriptor {
    /// Data represents signature data
    #[derive(Clone, PartialEq, ::prost::Message)]
    pub struct Data {
        /// sum is the oneof that specifies whether this represents single or multi-signature data
        #[prost(oneof="data::Sum", tags="1, 2")]
        pub sum: ::std::option::Option<data::Sum>,
    }
    pub mod data {
        /// Single is the signature data for a single signer
        #[derive(Clone, PartialEq, ::prost::Message)]
        pub struct Single {
            /// mode is the signing mode of the single signer
            #[prost(enumeration="super::super::SignMode", tag="1")]
            pub mode: i32,
            /// signature is the raw signature bytes
            #[prost(bytes, tag="2")]
            pub signature: std::vec::Vec<u8>,
        }
        /// Multi is the signature data for a multisig public key
        #[derive(Clone, PartialEq, ::prost::Message)]
        pub struct Multi {
            /// bitarray specifies which keys within the multisig are signing
            #[prost(message, optional, tag="1")]
            pub bitarray: ::std::option::Option<super::super::super::super::super::base::crypto::v1beta1::CompactBitArray>,
            /// signatures is the signatures of the multi-signature
            #[prost(message, repeated, tag="2")]
            pub signatures: ::std::vec::Vec<super::Data>,
        }
        /// sum is the oneof that specifies whether this represents single or multi-signature data
        #[derive(Clone, PartialEq, ::prost::Oneof)]
        pub enum Sum {
            /// single represents a single signer
            #[prost(message, tag="1")]
            Single(Single),
            /// multi represents a multisig signer
            #[prost(message, tag="2")]
            Multi(Multi),
        }
    }
}
/// SignMode represents a signing mode with its own security guarantees.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, ::prost::Enumeration)]
#[repr(i32)]
pub enum SignMode {
    /// SIGN_MODE_UNSPECIFIED specifies an unknown signing mode and will be rejected
    Unspecified = 0,
    /// SIGN_MODE_DIRECT specifies a signing mode which uses SignDoc and is verified
    /// with raw bytes from Tx
    Direct = 1,
    /// SIGN_MODE_TEXTUAL is a future signing mode that will verify some human-readable
    /// textual representation on top of the binary representation from SIGN_MODE_DIRECT
    Textual = 2,
    /// SIGN_MODE_LEGACY_AMINO_JSON is a backwards compatibility mode which uses
    /// Amino JSON and will be removed in the future
    LegacyAminoJson = 127,
}
