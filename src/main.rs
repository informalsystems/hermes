use rand_core::OsRng;
// use secp256k1::{Message, PublicKey, Secp256k1, SecretKey};
use hex;
use std::num::ParseIntError;

use prost::bytes::Buf;

use k256::{
    ecdsa::{signature::Signer, signature::Verifier, Signature, SigningKey, VerifyKey},
    EncodedPoint, SecretKey,
};

// Use this for account
// use tendermint::amino_types::message::AminoMessage;
// use tendermint::account::Id;
// use tendermint::public_key::Ed25519 as TMEd25519;
// use tendermint::public_key::PublicKey as TMPublicKey;
// use tendermint::TendermintKey;
// use subtle_encoding::{base64, bech32, hex};

/*#[derive(Debug)]
pub struct KeyPairSecp256k1 {
    pub secret: SecretKey,
    pub public: PublicKey,
}*/

#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Coin {
    #[prost(string, tag = "1")]
    pub denom: std::string::String,
    #[prost(string, tag = "2")]
    pub amount: std::string::String,
}

#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgSend {
    #[prost(bytes, tag = "1")]
    pub from_address: std::vec::Vec<u8>,
    #[prost(bytes, tag = "2")]
    pub to_address: std::vec::Vec<u8>,
    #[prost(message, repeated, tag = "3")]
    pub amount: ::std::vec::Vec<Coin>,
}

/// sum specifies which type of public key is wrapped
#[derive(Clone, PartialEq, ::prost::Oneof)]
pub enum PKSum {
    #[prost(bytes, tag = "1")]
    Secp256k1(std::vec::Vec<u8>),
    #[prost(bytes, tag = "2")]
    Ed25519(std::vec::Vec<u8>),
}

/// SignDoc is the type used for generating sign bytes for SIGN_MODE_DIRECT.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SignDoc {
    /// body_bytes is protobuf serialization of a TxBody that matches the representation in TxRaw.
    #[prost(bytes, tag = "1")]
    pub body_bytes: std::vec::Vec<u8>,
    /// auth_info_bytes is a protobuf serialization of an AuthInfo that matches the representation in TxRaw.
    #[prost(bytes, tag = "2")]
    pub auth_info_bytes: std::vec::Vec<u8>,
    /// chain_id is the unique identifier of the chain this transaction targets.
    /// It prevents signed transactions from being used on another chain by an
    /// attacker
    #[prost(string, tag = "3")]
    pub chain_id: std::string::String,
    /// account_number is the account number of the account in state
    #[prost(uint64, tag = "4")]
    pub account_number: u64,
}
/// TxBody is the body of a transaction that all signers sign over.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct TxBody {
    /// messages is a list of messages to be executed. The required signers of those messages define
    /// the number and order of elements in AuthInfo's signer_infos and Tx's signatures.
    /// Each required signer address is added to the list only the first time it occurs.
    ///
    /// By convention, the first required signer (usually from the first message) is referred
    /// to as the primary signer and pays the fee for the whole transaction.
    #[prost(message, repeated, tag = "1")]
    pub messages: ::std::vec::Vec<::prost_types::Any>,
    /// memo is any arbitrary memo to be added to the transaction
    #[prost(string, tag = "2")]
    pub memo: std::string::String,
    /// timeout is the block height after which this transaction will not
    /// be processed by the chain
    #[prost(uint64, tag = "3")]
    pub timeout_height: u64,
    /// extension_options are arbitrary options that can be added by chains
    /// when the default options are not sufficient. If any of these are present
    /// and can't be handled, the transaction will be rejected
    #[prost(message, repeated, tag = "1023")]
    pub extension_options: ::std::vec::Vec<::prost_types::Any>,
    /// extension_options are arbitrary options that can be added by chains
    /// when the default options are not sufficient. If any of these are present
    /// and can't be handled, they will be ignored
    #[prost(message, repeated, tag = "2047")]
    pub non_critical_extension_options: ::std::vec::Vec<::prost_types::Any>,
}
/// AuthInfo describes the fee and signer modes that are used to sign a transaction.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct AuthInfo {
    /// signer_infos defines the signing modes for the required signers. The number
    /// and order of elements must match the required signers from TxBody's messages.
    /// The first element is the primary signer and the one which pays the fee.
    #[prost(message, repeated, tag = "1")]
    pub signer_infos: ::std::vec::Vec<SignerInfo>,
    /// Fee is the fee and gas limit for the transaction. The first signer is the
    /// primary signer and the one which pays the fee. The fee can be calculated
    /// based on the cost of evaluating the body and doing signature verification
    /// of the signers. This can be estimated via simulation.
    #[prost(message, optional, tag = "2")]
    pub fee: ::std::option::Option<Fee>,
}

/// Fee includes the amount of coins paid in fees and the maximum
/// gas to be used by the transaction. The ratio yields an effective "gasprice",
/// which must be above some miminum to be accepted into the mempool.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Fee {
    /// amount is the amount of coins to be paid as a fee
    #[prost(message, repeated, tag = "1")]
    pub amount: ::std::vec::Vec<Coin>,
    /// gas_limit is the maximum gas that can be used in transaction processing
    /// before an out of gas error occurs
    #[prost(uint64, tag = "2")]
    pub gas_limit: u64,
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

/// SignerInfo describes the public key and signing mode of a single top-level signer.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SignerInfo {
    /// public_key is the public key of the signer. It is optional for accounts
    /// that already exist in state. If unset, the verifier can use the required \
    /// signer address for this position and lookup the public key.
    #[prost(message, optional, tag = "1")]
    pub public_key: ::std::option::Option<PK>,
    /// mode_info describes the signing mode of the signer and is a nested
    /// structure to support nested multisig pubkey's
    #[prost(message, optional, tag = "2")]
    pub mode_info: ::std::option::Option<ModeInfo>,
    /// sequence is the sequence of the account, which describes the
    /// number of committed transactions signed by a given address. It is used to prevent
    /// replay attacks.
    #[prost(uint64, tag = "3")]
    pub sequence: u64,
}
/// ModeInfo describes the signing mode of a single or nested multisig signer.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ModeInfo {
    /// sum is the oneof that specifies whether this represents a single or nested
    /// multisig signer
    #[prost(oneof = "Sum", tags = "1, 2")]
    pub sum: ::std::option::Option<Sum>,
}

/// Single is the mode info for a single signer. It is structured as a message
/// to allow for additional fields such as locale for SIGN_MODE_TEXTUAL in the future
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Single {
    /// mode is the signing mode of the single signer
    #[prost(enumeration = "SignMode", tag = "1")]
    pub mode: i32,
}

/// CompactBitArray is an implementation of a space efficient bit array.
/// This is used to ensure that the encoded data takes up a minimal amount of
/// space after proto encoding.
/// This is not thread safe, and is not intended for concurrent usage.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct CompactBitArray {
    #[prost(uint32, tag = "1")]
    pub extra_bits_stored: u32,
    #[prost(bytes, tag = "2")]
    pub elems: std::vec::Vec<u8>,
}

/// Multi is the mode info for a multisig public key
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Multi {
    /// bitarray specifies which keys within the multisig are signing
    #[prost(message, optional, tag = "1")]
    pub bitarray: ::std::option::Option<CompactBitArray>,
    /// mode_infos is the corresponding modes of the signers of the multisig
    /// which could include nested multisig public keys
    #[prost(message, repeated, tag = "2")]
    pub mode_infos: ::std::vec::Vec<ModeInfo>,
}
/// sum is the oneof that specifies whether this represents a single or nested
/// multisig signer
#[derive(Clone, PartialEq, ::prost::Oneof)]
pub enum Sum {
    /// single represents a single signer
    #[prost(message, tag = "1")]
    Single(Single),
    /// multi represents a nested multisig signer
    #[prost(message, tag = "2")]
    Multi(Multi),
}

/// PublicKey specifies a public key
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct PK {
    /// sum specifies which type of public key is wrapped
    #[prost(oneof = "PKSum", tags = "1, 2, 3, 4, 5, 15")]
    pub sum: ::std::option::Option<PKSum>,
}

/// TxRaw is a variant of Tx that pins the signer's exact binary representation of body and
/// auth_info. This is used for signing, broadcasting and verification. The binary
/// `serialize(tx: TxRaw)` is stored in Tendermint and the hash `sha256(serialize(tx: TxRaw))`
/// becomes the "txhash", commonly used as the transaction ID.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct TxRaw {
    /// body_bytes is a protobuf serialization of a TxBody that matches the representation in SignDoc.
    #[prost(bytes, tag = "1")]
    pub body_bytes: std::vec::Vec<u8>,
    /// auth_info_bytes is a protobuf serialization of an AuthInfo that matches the representation in SignDoc.
    #[prost(bytes, tag = "2")]
    pub auth_info_bytes: std::vec::Vec<u8>,
    /// signatures is a list of signatures that matches the length and order of AuthInfo's signer_infos to
    /// allow connecting signature meta information like public key and signing mode by position.
    #[prost(bytes, repeated, tag = "3")]
    pub signatures: ::std::vec::Vec<std::vec::Vec<u8>>,
}

fn get_account(pk: Vec<u8>) -> Vec<u8> {
    use crypto::digest::Digest;
    use crypto::ripemd160::Ripemd160;
    use crypto::sha2::Sha256;
    let mut seed = Sha256::new();
    seed.input(pk.as_slice());
    let mut bytes = vec![0; seed.output_bytes()];
    seed.result(&mut bytes);

    let mut hash = Ripemd160::new();
    hash.input(bytes.as_slice());
    let mut acct = vec![0; hash.output_bytes()];
    hash.result(&mut acct);
    acct.to_vec()
}

// Couldnt get this to work because of conflicting with other secp256k1 library
/*fn get_bech32(acct: &str) -> String {
    let pk = PublicKey::Secp256k1(Secp256k1::from_bytes(&hex::decode_upper(acct)));
    let tmkey = TendermintKey::AccountKey(pk);
    tmkey.to_bech32("cosmospub")
}*/

fn main() {
    // This is a pregenerated private key from running:
    //      let signing_key = SigningKey::random(&mut OsRng);
    //      println!("{:?", hex::encode(signing_key.to_bytes()));
    // It corresponds to the address: cosmos14kl05amnc3mdyj5d2r27agvwhuqgz7vwfz0wwj
    // Add it to your genesis or send coins to it.
    // Then query the account number and update account_number here.
    let signing_key_bytes = "cda4e48a1ae228656e483b2f3ae7bca6d04abcef64189ff56d481987259dd2a4";
    let account_number = 12;

    // This is the hex addr for an account to send funds to. Doesn't really matter what this is,
    // any 20 bytes will do ...
    let to_addr_hex = "A31C303AB94732D493FEF4699AC7C199D71D3660";

    let signing_key = SigningKey::new(&hex::decode(signing_key_bytes).unwrap()).unwrap();
    let verify_key = VerifyKey::from(&signing_key);
    let pubkey_bytes = verify_key.to_bytes().to_vec();
    let addr = get_account(pubkey_bytes.clone());

    let coin = Coin {
        denom: "stake".to_string(),
        amount: "1000".to_string(),
    };

    let msg = MsgSend {
        from_address: addr.to_vec(),
        to_address: hex::decode(to_addr_hex).unwrap(),
        amount: vec![coin],
    };

    let mut proto_msgs: Vec<prost_types::Any> = Vec::new();
    let mut buf = Vec::new();

    // Have a loop if new_builder takes more messages
    // for now just encode one message
    prost::Message::encode(&msg, &mut buf).unwrap();

    // Create a MsgSend proto Any message
    let any_msg = prost_types::Any {
        type_url: "/cosmos.bank.v1beta1.MsgSend".to_string(),
        value: buf,
    };

    // Add proto message
    proto_msgs.push(any_msg);

    // Create TxBody
    let body = TxBody {
        messages: proto_msgs,
        memo: "".to_string(),
        timeout_height: 0,
        extension_options: Vec::<prost_types::Any>::new(),
        non_critical_extension_options: Vec::<prost_types::Any>::new(),
    };

    let sum = Some(PKSum::Secp256k1(pubkey_bytes));
    let pk = Some(PK { sum });

    let single = Single { mode: 1 };
    let sum_single = Some(Sum::Single(single));
    let mode = Some(ModeInfo { sum: sum_single });

    let signer_info = SignerInfo {
        public_key: pk,
        mode_info: mode,
        sequence: 0,
    };

    let coin = Coin {
        denom: "stake".to_string(),
        amount: "11".to_string(),
    };

    let fee = Some(Fee {
        amount: vec![coin],
        gas_limit: 100000,
    });

    let auth_info = AuthInfo {
        signer_infos: vec![signer_info],
        fee,
    };

    // A protobuf serialization of a TxBody
    let mut body_bytes = Vec::new();
    prost::Message::encode(&body, &mut body_bytes).unwrap();

    // A protobuf serialization of a AuthInfo
    let mut auth_bytes = Vec::new();
    prost::Message::encode(&auth_info, &mut auth_bytes).unwrap();

    let sign_doc = SignDoc {
        body_bytes: body_bytes.clone(),
        auth_info_bytes: auth_bytes.clone(),
        chain_id: "testing".to_string(),
        account_number: account_number,
    };

    // A protobuf serialization of a SignDoc
    let mut signdoc_buf = Vec::new();
    prost::Message::encode(&sign_doc, &mut signdoc_buf).unwrap();

    let signature: Signature = signing_key.sign(&signdoc_buf);

    let tx_raw = TxRaw {
        body_bytes,
        auth_info_bytes: auth_bytes,
        signatures: vec![signature.as_ref().to_vec()],
    };

    let mut txraw_buf = Vec::new();
    prost::Message::encode(&tx_raw, &mut txraw_buf).unwrap();
    println!("Now broadcast this!");
    println!("TxRAW {:?}", hex::encode(txraw_buf.clone()));
}
