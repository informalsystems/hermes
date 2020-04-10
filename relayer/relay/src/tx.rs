use serde::{Deserialize, Serialize};
use serde_json;
use std::time::Duration;

use tendermint::block::{Commit, Header};
use tendermint::{serializers, validator};

use stdtx;
use stdtx::amino_types::{StdFee, StdSignature};
use stdtx::type_name::TypeName;

// Work in progress for Amino and AminoJSON encoding of a CreateClient transaction.
//
// Current State:
// - Only works for JSON
// - JSON marshalled StdTx can be signed by gaiacli (!)
// - Signed StdTx JSON can be unmarshalled
//
// TODO:
// - Generalize JSON decoding
// - Marshal to Amino (make better use of Iqlusion's StdTx?)

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct SignedHeaderVals {
    pub SignedHeader: SignedHeader, // XXX: this should be unrolled in the Go ...
    pub validator_set: validator::Set,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct SignedHeader {
    pub header: Header,
    pub commit: Commit,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct MsgCreateClient {
    #[serde(rename = "type")]
    pub name: String,
    pub value: MsgCreateClientInner,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct MsgCreateClientInner {
    pub client_id: String,
    pub header: SignedHeaderVals,
    #[serde(
        serialize_with = "serializers::serialize_duration",
        deserialize_with = "serializers::parse_duration"
    )]
    pub trusting_period: Duration,
    #[serde(
        serialize_with = "serializers::serialize_duration",
        deserialize_with = "serializers::parse_duration"
    )]
    pub unbonding_period: Duration,
    pub address: stdtx::Address,
}

impl MsgCreateClientInner {
    // wrap it in the amino name
    fn typed_msg(self) -> MsgCreateClient {
        MsgCreateClient {
            name: "ibc/client/MsgCreateClient".to_string(),
            value: self,
        }
    }
}

fn std_tx<M>(msg: M, gas: u64, memo: &str) -> StdTx<M> {
    let mut msgs = Vec::new();
    msgs.push(msg);
    StdTx {
        name: "cosmos-sdk/StdTx".to_string(),
        value: StdTxInner {
            msg: msgs,
            fee: StdFee::for_gas(gas),
            memo: memo.to_owned(),
            signatures: Vec::new(),
        },
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StdTx<M> {
    #[serde(rename = "type")]
    name: String,
    value: StdTxInner<M>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StdTxInner<M> {
    pub msg: Vec<M>, // XXX name should be msgs ...
    pub fee: StdFee,
    pub signatures: Vec<StdSignature>,
    pub memo: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::amino;
    use crate::error;

    use std::fs;
    use std::fs::File;
    use std::io::prelude::*;
    use std::path::Path;

    use tendermint::rpc::Client as RpcClient;

    use prost_amino::Message;

    use subtle_encoding::hex;

    fn to_hex(bytes: &[u8]) -> String {
        let hex_bytes = hex::encode(bytes);
        String::from_utf8(hex_bytes).unwrap()
    }

    fn msg_create_client() -> MsgCreateClientInner {
        let rpc_client = RpcClient::new("localhost:26657".parse().unwrap());
        let commit = block_on(rpc_client.latest_commit())
            .map_err(|e| error::Kind::Rpc.context(e))
            .unwrap();

        let validators = block_on(rpc_client.validators(commit.signed_header.header.height))
            .map_err(|e| error::Kind::Rpc.context(e))
            .unwrap();

        let shv = SignedHeaderVals {
            SignedHeader: SignedHeader {
                header: commit.signed_header.header,
                commit: commit.signed_header.commit,
            },
            validator_set: validator::Set::new(validators.validators),
        };

        let tp = Duration::new(10000, 0);
        let up = Duration::new(1000000, 0);
        let (_hrp, address) =
            stdtx::Address::from_bech32("cosmos1q6zae0v7jx5lq9ucu9qclls05enya987n684cd").unwrap();

        MsgCreateClientInner {
            client_id: "someclient".to_string(),
            header: shv,
            trusting_period: tp,
            unbonding_period: up,
            address: address,
        }
    }

    // amino encode msg
    #[test]
    fn test_amino() {
        let msg = msg_create_client();
        let amino_msg = amino::MsgCreateClient::from(&msg);
        let type_name = TypeName::new("ibc/client/MsgCreateClient").unwrap();
        let mut amino_bytes = type_name.amino_prefix();
        amino_msg
            .encode(&mut amino_bytes)
            .expect("LEB128 encoding error");
        println!("{:?}", to_hex(&amino_bytes));
    }

    // make a StdTx with MsgCreateClient from a local node.
    // save it to "unsigned.json".
    // this file can be successfully signed with gaiacli!
    #[test]
    fn test_create_client() {
        let msg = msg_create_client();

        let tx = std_tx(msg.typed_msg(), 3000, "mymemo");
        println!("{:?}", tx);

        let j = serde_json::to_string_pretty(&tx).unwrap();
        println!("JSON");
        println!("{}", j);

        let path = Path::new("unsigned.json");

        let mut file = File::create(&path).unwrap();
        file.write_all(j.as_bytes());
    }

    fn printer(name: &str, o: impl Message) {
        // let type_name = TypeName::new("ibc/client/MsgCreateClient").unwrap();
        // let mut amino_bytes = type_name.amino_prefix();
        let mut amino_bytes = Vec::new();
        o.encode(&mut amino_bytes).expect("LEB128 encoding error");
        println!("{} -----------------------------", name);
        println!("{:?}", to_hex(&amino_bytes));
    }

    // load signed.json from file and unmarshal it.
    // the unmarshalling works.
    #[test]
    fn test_broadcast_create_client() {
        //let rpc_client = RpcClient::new("localhost:26657".parse().unwrap());

        let contents = fs::read_to_string("signed.json").unwrap();
        let tx: StdTx<MsgCreateClient> = serde_json::from_str(&contents).unwrap(); // TODO generalize
        println!("{:?}", tx);

        let msg = &tx.value.msg[0].value;
        let msg = &amino::MsgCreateClient::from(msg);

        let hcv = msg.header.as_ref().unwrap();
        let sh = hcv.SignedHeader.as_ref().unwrap();

        let header = sh.header.as_ref().unwrap();
        let commit = sh.commit.as_ref().unwrap();
        let vals = hcv.validator_set.as_ref().unwrap();
        printer("header", header.clone());
        printer("commit", commit.clone());
        printer("vals", vals.clone());

        printer("hcv", hcv.clone());
        printer("sh", sh.clone());

        let type_name = TypeName::new("ibc/client/MsgCreateClient").unwrap();
        let mut amino_bytes = type_name.amino_prefix();
        msg.encode(&mut amino_bytes).expect("LEB128 encoding error");
        println!("MSG--------------------------");
        println!("{:?}", to_hex(&amino_bytes));
    }
}

use std::future::Future;

fn block_on<F: Future>(future: F) -> F::Output {
    tokio::runtime::Builder::new()
        .basic_scheduler()
        .enable_all()
        .build()
        .unwrap()
        .block_on(future)
}
