use ibc::core::ics04_channel::packet::Packet;
use ibc_proto::ibc::applications::query::v1::CrossChainQuery;
use prost::DecodeError;
use reqwest;
use reqwest::Error;
// use ibc_proto::ibc::applications::transfer::v1::MsgTransfer;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug)]
pub struct MsgTransfer {
    pub amount: String,
    pub denom: String,
    pub receiver: String,
    pub sender: String,
}

pub async fn rest_query(uri: String) -> Result<String, Error> {
    reqwest::get(uri).await?.text().await
}

// Check if packet data is encoded byte-stream with CrossChainQuery msg
pub fn check_if_cross_chain_query_packet(packet: Option<&Packet>) -> bool {
    match packet {
        Some(packet) => {
            let packet_data = packet.data.as_slice();
            let decoded: Result<CrossChainQuery, DecodeError> = prost::Message::decode(packet_data);
            match decoded {
                Ok(msg) => {
                    if msg.msg_type == "cross_chain_query" {
                        true
                    } else {
                        false
                    }
                }
                Err(_) => false,
            }
        }
        None => false
    }
}
