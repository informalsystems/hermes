/// SignatureDescriptors wraps multiple SignatureDescriptor's.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SignatureDescriptors {
    /// signatures are the signature descriptors
    #[prost(message, repeated, tag="1")]
    pub signatures: ::prost::alloc::vec::Vec<SignatureDescriptor>,
}
/// SignatureDescriptor is a convenience type which represents the full data for
/// a signature including the public key of the signer, signing modes and the
/// signature itself. It is primarily used for coordinating signatures between
/// clients.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SignatureDescriptor {
    /// public_key is the public key of the signer
    #[prost(message, optional, tag="1")]
    pub public_key: ::core::option::Option<super::super::super::super::google::protobuf::Any>,
    #[prost(message, optional, tag="2")]
    pub data: ::core::option::Option<signature_descriptor::Data>,
    /// sequence is the sequence of the account, which describes the
    /// number of committed transactions signed by a given address. It is used to prevent
    /// replay attacks.
    #[prost(uint64, tag="3")]
    pub sequence: u64,
}
/// Nested message and enum types in `SignatureDescriptor`.
pub mod signature_descriptor {
    /// Data represents signature data
    #[derive(Clone, PartialEq, ::prost::Message)]
    pub struct Data {
        /// sum is the oneof that specifies whether this represents single or multi-signature data
        #[prost(oneof="data::Sum", tags="1, 2")]
        pub sum: ::core::option::Option<data::Sum>,
    }
    /// Nested message and enum types in `Data`.
    pub mod data {
        /// Single is the signature data for a single signer
        #[derive(Clone, PartialEq, ::prost::Message)]
        pub struct Single {
            /// mode is the signing mode of the single signer
            #[prost(enumeration="super::super::SignMode", tag="1")]
            pub mode: i32,
            /// signature is the raw signature bytes
            #[prost(bytes="vec", tag="2")]
            pub signature: ::prost::alloc::vec::Vec<u8>,
        }
        /// Multi is the signature data for a multisig public key
        #[derive(Clone, PartialEq, ::prost::Message)]
        pub struct Multi {
            /// bitarray specifies which keys within the multisig are signing
            #[prost(message, optional, tag="1")]
            pub bitarray: ::core::option::Option<super::super::super::super::super::crypto::multisig::v1beta1::CompactBitArray>,
            /// signatures is the signatures of the multi-signature
            #[prost(message, repeated, tag="2")]
            pub signatures: ::prost::alloc::vec::Vec<super::Data>,
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
    /// SIGN_MODE_UNSPECIFIED specifies an unknown signing mode and will be
    /// rejected
    Unspecified = 0,
    /// SIGN_MODE_DIRECT specifies a signing mode which uses SignDoc and is
    /// verified with raw bytes from Tx
    Direct = 1,
    /// SIGN_MODE_TEXTUAL is a future signing mode that will verify some
    /// human-readable textual representation on top of the binary representation
    /// from SIGN_MODE_DIRECT
    Textual = 2,
    /// SIGN_MODE_LEGACY_AMINO_JSON is a backwards compatibility mode which uses
    /// Amino JSON and will be removed in the future
    LegacyAminoJson = 127,
    /// SIGN_MODE_EIP_191 specifies the sign mode for EIP 191 signing on the Cosmos
    /// SDK. Ref: <https://eips.ethereum.org/EIPS/eip-191>
    ///
    /// Currently, SIGN_MODE_EIP_191 is registered as a SignMode enum variant,
    /// but is not implemented on the SDK by default. To enable EIP-191, you need
    /// to pass a custom `TxConfig` that has an implementation of
    /// `SignModeHandler` for EIP-191. The SDK may decide to fully support
    /// EIP-191 in the future.
    ///
    /// Since: cosmos-sdk 0.45.2
    Eip191 = 191,
}
impl SignMode {
    /// String value of the enum field names used in the ProtoBuf definition.
    ///
    /// The values are not transformed in any way and thus are considered stable
    /// (if the ProtoBuf definition does not change) and safe for programmatic use.
    pub fn as_str_name(&self) -> &'static str {
        match self {
            SignMode::Unspecified => "SIGN_MODE_UNSPECIFIED",
            SignMode::Direct => "SIGN_MODE_DIRECT",
            SignMode::Textual => "SIGN_MODE_TEXTUAL",
            SignMode::LegacyAminoJson => "SIGN_MODE_LEGACY_AMINO_JSON",
            SignMode::Eip191 => "SIGN_MODE_EIP_191",
        }
    }
}
