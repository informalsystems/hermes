use ibc_proto::google::protobuf::Any;
use secp256k1::PublicKey;

const TYPE_URL: &str = "/cosmos.crypto.secp256k1.PubKey";

pub fn encode_public_key(public_key: &PublicKey) -> Any {
    let key_bytes = public_key.serialize();

    Any {
        type_url: TYPE_URL.to_string(),
        value: key_bytes.into(),
    }
}
