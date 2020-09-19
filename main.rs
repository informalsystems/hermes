// Signer
use signatory_secp256k1::{SecretKey, EcdsaSigner};
use ecdsa::curve::Secp256k1;

use ecdsa::FixedSignature;
use signature::Signer;
use std::convert::TryInto;
use signatory_secp256k1::signatory::sha2;
use signatory_secp256k1::signatory::public_key::PublicKeyed;
use sha2::{Digest, Sha256};
use std::num::ParseIntError;
use ecdsa::elliptic_curve::generic_array::GenericArray;

pub type FSignature = FixedSignature<Secp256k1>;

// Proto types

#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Coin {
    #[prost(string, tag="1")]
    pub denom: std::string::String,
    #[prost(string, tag="2")]
    pub amount: std::string::String,
}

#[derive(Clone, PartialEq, ::prost::Message)]
pub struct MsgSend {
    #[prost(bytes, tag="1")]
    pub from_address: std::vec::Vec<u8>,
    #[prost(bytes, tag="2")]
    pub to_address: std::vec::Vec<u8>,
    #[prost(message, repeated, tag="3")]
    pub amount: ::std::vec::Vec<Coin>,
}

/// sum specifies which type of public key is wrapped
#[derive(Clone, PartialEq, ::prost::Oneof)]
pub enum PKSum {
    #[prost(bytes, tag="1")]
    Secp256k1(std::vec::Vec<u8>)
}

/// SignDoc is the type used for generating sign bytes for SIGN_MODE_DIRECT.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct SignDoc {
    /// body_bytes is protobuf serialization of a TxBody that matches the representation in TxRaw.
    #[prost(bytes, tag="1")]
    pub body_bytes: std::vec::Vec<u8>,
    /// auth_info_bytes is a protobuf serialization of an AuthInfo that matches the representation in TxRaw.
    #[prost(bytes, tag="2")]
    pub auth_info_bytes: std::vec::Vec<u8>,
    /// chain_id is the unique identifier of the chain this transaction targets.
    /// It prevents signed transactions from being used on another chain by an
    /// attacker
    #[prost(string, tag="3")]
    pub chain_id: std::string::String,
    /// account_number is the account number of the account in state
    #[prost(uint64, tag="4")]
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
    #[prost(message, repeated, tag="1")]
    pub messages: ::std::vec::Vec<::prost_types::Any>,
    /// memo is any arbitrary memo to be added to the transaction
    #[prost(string, tag="2")]
    pub memo: std::string::String,
    /// timeout is the block height after which this transaction will not
    /// be processed by the chain
    #[prost(uint64, tag="3")]
    pub timeout_height: u64,
    /// extension_options are arbitrary options that can be added by chains
    /// when the default options are not sufficient. If any of these are present
    /// and can't be handled, the transaction will be rejected
    #[prost(message, repeated, tag="1023")]
    pub extension_options: ::std::vec::Vec<::prost_types::Any>,
    /// extension_options are arbitrary options that can be added by chains
    /// when the default options are not sufficient. If any of these are present
    /// and can't be handled, they will be ignored
    #[prost(message, repeated, tag="2047")]
    pub non_critical_extension_options: ::std::vec::Vec<::prost_types::Any>,
}
/// AuthInfo describes the fee and signer modes that are used to sign a transaction.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct AuthInfo {
    /// signer_infos defines the signing modes for the required signers. The number
    /// and order of elements must match the required signers from TxBody's messages.
    /// The first element is the primary signer and the one which pays the fee.
    #[prost(message, repeated, tag="1")]
    pub signer_infos: ::std::vec::Vec<SignerInfo>,
    /// Fee is the fee and gas limit for the transaction. The first signer is the
    /// primary signer and the one which pays the fee. The fee can be calculated
    /// based on the cost of evaluating the body and doing signature verification
    /// of the signers. This can be estimated via simulation.
    #[prost(message, optional, tag="2")]
    pub fee: ::std::option::Option<Fee>,
}

/// Fee includes the amount of coins paid in fees and the maximum
/// gas to be used by the transaction. The ratio yields an effective "gasprice",
/// which must be above some miminum to be accepted into the mempool.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Fee {
    /// amount is the amount of coins to be paid as a fee
    #[prost(message, repeated, tag="1")]
    pub amount: ::std::vec::Vec<Coin>,
    /// gas_limit is the maximum gas that can be used in transaction processing
    /// before an out of gas error occurs
    #[prost(uint64, tag="2")]
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
    #[prost(message, optional, tag="1")]
    pub public_key: ::std::option::Option<PublicKey>,
    /// mode_info describes the signing mode of the signer and is a nested
    /// structure to support nested multisig pubkey's
    #[prost(message, optional, tag="2")]
    pub mode_info: ::std::option::Option<ModeInfo>,
    /// sequence is the sequence of the account, which describes the
    /// number of committed transactions signed by a given address. It is used to prevent
    /// replay attacks.
    #[prost(uint64, tag="3")]
    pub sequence: u64,
}
/// ModeInfo describes the signing mode of a single or nested multisig signer.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ModeInfo {
    /// sum is the oneof that specifies whether this represents a single or nested
    /// multisig signer
    #[prost(oneof="Sum", tags="1, 2")]
    pub sum: ::std::option::Option<Sum>,
}

/// Single is the mode info for a single signer. It is structured as a message
/// to allow for additional fields such as locale for SIGN_MODE_TEXTUAL in the future
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Single {
    /// mode is the signing mode of the single signer
    #[prost(enumeration="SignMode", tag="1")]
    pub mode: i32,
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

/// Multi is the mode info for a multisig public key
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Multi {
    /// bitarray specifies which keys within the multisig are signing
    #[prost(message, optional, tag="1")]
    pub bitarray: ::std::option::Option<CompactBitArray>,
    /// mode_infos is the corresponding modes of the signers of the multisig
    /// which could include nested multisig public keys
    #[prost(message, repeated, tag="2")]
    pub mode_infos: ::std::vec::Vec<ModeInfo>,
}
/// sum is the oneof that specifies whether this represents a single or nested
/// multisig signer
#[derive(Clone, PartialEq, ::prost::Oneof)]
pub enum Sum {
    /// single represents a single signer
    #[prost(message, tag="1")]
    Single(Single),
    /// multi represents a nested multisig signer
    #[prost(message, tag="2")]
    Multi(Multi),
}

/// PublicKey specifies a public key
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct PublicKey {
    /// sum specifies which type of public key is wrapped
    #[prost(oneof="PKSum", tags="1, 2, 3, 4, 5, 15")]
    pub sum: ::std::option::Option<PKSum>,
}

/// TxRaw is a variant of Tx that pins the signer's exact binary representation of body and
/// auth_info. This is used for signing, broadcasting and verification. The binary
/// `serialize(tx: TxRaw)` is stored in Tendermint and the hash `sha256(serialize(tx: TxRaw))`
/// becomes the "txhash", commonly used as the transaction ID.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct TxRaw {
    /// body_bytes is a protobuf serialization of a TxBody that matches the representation in SignDoc.
    #[prost(bytes, tag="1")]
    pub body_bytes: std::vec::Vec<u8>,
    /// auth_info_bytes is a protobuf serialization of an AuthInfo that matches the representation in SignDoc.
    #[prost(bytes, tag="2")]
    pub auth_info_bytes: std::vec::Vec<u8>,
    /// signatures is a list of signatures that matches the length and order of AuthInfo's signer_infos to
    /// allow connecting signature meta information like public key and signing mode by position.
    #[prost(bytes, repeated, tag="3")]
    pub signatures: ::std::vec::Vec<std::vec::Vec<u8>>,
}

fn main() {

    // Signer
    const VALIDATOR_ADDR: &'static str = "064A6FC334BADB830F1C7192641F6E99BC85BE0C";
    const BOB_ADDR: &'static str = "7B72B907C4EE8B46D19B9C4A34BDA0CC285F6488";
    const VALIDATOR_PRIVATE_KEY: &'static str = "BEB22FAAEE71750277290BA57606ABFC75AD02A0C4A08700F8CF6CFD9108D4D44FBCFD6F8293968AB8E414399BF8499D91A00EFA4AF42BDB26DEA0CF5158A29F" ;

    use crypto::ed25519;
    use crypto::sha2::Sha256;
    use crypto::digest::Digest;

    let phrase = "purchase hobby popular celery evil fantasy someone party position gossip host gather";
    let mut seed = Sha256::new();
    seed.input_str(&phrase);
    let mut bytes = vec![0; seed.output_bytes()];
    seed.result(&mut bytes);

    let (_priv, _publ) = ed25519::keypair(&bytes); // expects slice
    println!("{:?}|{:?}", _priv.to_vec(), _publ.to_vec());
    //let priv_key = decode_hex(VALIDATOR_PRIVATE_KEY).unwrap();
    /*let secret = &SecretKey::from_bytes(priv_key.as_slice());
    let s2 = &SecretKey::new(priv_key.as_slice());
    match secret {
        Ok(s) => {
            let signer = EcdsaSigner::from(secret);
            let pk_value = signer.public_key().unwrap();
            println!("Public Key:{:?}", pk_value.as_bytes().to_vec());
        }
        Err(e) => println!("Error getting secret:{:?}", e)
    }


    std::process::abort();*/

/*    let sha_digest = Sha256::digest(pk_value.as_bytes());
    let ripemd_digest = Ripemd160::digest(&sha_digest[..]);
    let mut addr = [0u8; 20];
    addr.copy_from_slice(&ripemd_digest[..20]);*/
/*
    let coin = Coin {
        denom: "stake".to_string(),
        amount: "1000".to_string()
    };

    let msg = MsgSend {
        from_address: decode_hex(VALIDATOR_ADDR).unwrap(),
        to_address: decode_hex(BOB_ADDR).unwrap(),
        amount: vec![coin]
    };

    let mut proto_msgs: Vec<prost_types::Any> = Vec::new();
    let mut buf = Vec::new();

    // Have a loop if new_builder takes more messages
    // for now just encode one message
    prost::Message::encode(&msg, &mut buf).unwrap();

    // Create a proto any message
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

//    let pk_value = VALIDATOR_PUBKEY.to_string().into_bytes();

    let sum = Some(PKSum::Secp256k1(pk_value.as_bytes().to_vec()));
    let pk = Some(PublicKey { sum });

    let single = Single { mode: 1 };
    let sum_single = Some(Sum::Single(single));
    let mode = Some(ModeInfo{ sum: sum_single});

    let signer_info = SignerInfo {
        public_key: pk,
        mode_info: mode,
        sequence: 0
    };

    let coin = Coin {
        denom: "stake".to_string(),
        amount: "1001".to_string()
    };

    let fee = Some(Fee {
        amount: vec![coin],
        gas_limit: 30000
    });

    let auth_info = AuthInfo {
        signer_infos: vec![signer_info],
        fee
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
        account_number: 0
    };

    // A protobuf serialization of a SignDoc
    let mut signdoc_buf = Vec::new();
    prost::Message::encode(&sign_doc, &mut signdoc_buf).unwrap();
    //println!("{:?}", decode(signdoc_buf.clone()));
    // Sign the sign_doc. This is not a proper signing yet.

    let signed: FSignature = signer.sign(signdoc_buf.as_slice());
    //println!("{:?}", signed_doc);

    let tx_raw = TxRaw {
        body_bytes,
        auth_info_bytes: auth_bytes,
        signatures: vec![signdoc_buf]
    };

    let mut txraw_buf = Vec::new();
    prost::Message::encode(&tx_raw, &mut txraw_buf).unwrap();
    println!("TxRAW {:?}", decode(txraw_buf.clone()));

*/
}

pub fn decode(v: Vec<u8>) -> String {
    let mut decoded: String = String::new();
    for b in v.iter() {
        let byte = format!("{:01$x}",b, 2);
        decoded.push_str(byte.as_str());
        // print!("{}",byte);
    }
    decoded
}

pub fn decode_hex(s: &str) -> Result<Vec<u8>, ParseIntError> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16))
        .collect()
}

#[cfg(test)]
mod tests {

    use super::decode;

    #[derive(Clone, PartialEq, ::prost::Message)]
    pub struct Article {
        #[prost(string, tag="1")]
        pub title: std::string::String,
        #[prost(string, tag="2")]
        pub description: std::string::String,
        #[prost(uint64, tag="3")]
        pub created: u64,
        #[prost(uint64, tag="4")]
        pub updated: u64,
        #[prost(bool, tag="5")]
        pub public: bool,
        #[prost(bool, tag="6")]
        pub promoted: bool,
        #[prost(enumeration="Type", tag="7")]
        pub r#type: i32,
        #[prost(enumeration="Review", tag="8")]
        pub review: i32,
        #[prost(string, repeated, tag="9")]
        pub comments: ::std::vec::Vec<std::string::String>,
        #[prost(string, repeated, tag="10")]
        pub backlinks: ::std::vec::Vec<std::string::String>,
    }
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, ::prost::Enumeration)]
    #[repr(i32)]
    pub enum Type {
        Unset = 0,
        Images = 1,
        News = 2,
    }
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, ::prost::Enumeration)]
    #[repr(i32)]
    pub enum Review {
        Unspecified = 0,
        Accepted = 1,
        Rejected = 2,
    }

    /// ADR-27
    /// Ensure the test vector for Article.proto pass
    #[test]
    fn test_protobuf_serialization() {
        let article = Article {
            title: "The world needs change 🌳".to_string(),
            description: "".to_string(),
            created: 1596806111080,
            updated: 0,
            public: true,
            promoted: false,
            r#type: Type::News as i32,
            review: Review::Unspecified as i32,
            comments: vec!["Nice one".to_string(), "Thank you".to_string()],
            backlinks: vec![]
        };

        let adr_27 = "0a1b54686520776f726c64206e65656473206368616e676520f09f8cb318e8bebec8bc2e280138024a084e696365206f6e654a095468616e6b20796f75".to_string();
        // A protobuf serialization of a Article
        let mut article_buf = Vec::new();
        prost::Message::encode(&article, &mut article_buf).unwrap();

        //println!("{:?}", convert(article_buf.clone()));
        assert_eq!(decode(article_buf), adr_27);
    }
}


