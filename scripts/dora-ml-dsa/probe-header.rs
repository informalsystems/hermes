use prost::Message as _;
use serde_json::Value;
use tendermint::crypto::{default::signature::Verifier, signature::Verifier as _};
use tendermint::{block::signed_header::SignedHeader, validator::Set, Signature};
use tendermint_proto::{serializers::bytes::base64string, v0_38::types::LightBlock};

fn main() {
    let path = std::env::args()
        .nth(1)
        .expect("usage: probe-dora-header FIXTURE");
    let f: Value = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
    let bytes = |field: &str| -> Vec<u8> {
        base64string::deserialize(f[field].clone()).expect("fixture bytes")
    };
    let lb = LightBlock::decode(bytes("light_block").as_slice()).unwrap();
    let h: SignedHeader = lb.signed_header.unwrap().try_into().unwrap();
    let vals: Set = lb.validator_set.unwrap().try_into().unwrap();
    assert_eq!(vals.hash(), h.header.validators_hash);
    let validator = &vals.validators()[0];
    assert_eq!(
        validator.address.to_string().to_uppercase(),
        f["address"].as_str().unwrap()
    );
    assert_eq!(validator.pub_key.to_bytes(), bytes("public_key"));
    let mut sig = bytes("signature");
    let vote = bytes("vote_sign_bytes");
    assert!(Verifier::verify(
        validator.pub_key,
        &vote,
        &Signature::try_from(sig.as_slice()).unwrap(),
    )
    .is_ok());
    let i = sig.len() / 2;
    sig[i] ^= 1;
    assert!(Verifier::verify(
        validator.pub_key,
        &vote,
        &Signature::try_from(sig.as_slice()).unwrap(),
    )
    .is_err());
    assert!(Signature::try_from(&sig[..sig.len() - 1]).is_err());
    println!("PASS real Dora wire header, validator hash/address and empty-context ML-DSA-65 verification");
    println!("PASS mutated and truncated signatures rejected");
}
