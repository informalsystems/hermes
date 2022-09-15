use ibc_proto::ibc::applications::query::v1::CrossChainQuery;
use prost::DecodeError;
use reqwest;
use reqwest::Error;
// use ibc_proto::ibc::applications::transfer::v1::MsgTransfer;
use crate::event::IbcEventWithHeight;
use ibc::core::ics04_channel::events::SendPacket;
use ibc::events::IbcEvent;
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

// SendPacket to CrossChainQuery
pub fn to_cross_chain_query_event_or_default(
    event_with_height: IbcEventWithHeight,
) -> IbcEventWithHeight {
    let height = event_with_height.clone().height;
    let event = event_with_height.clone().event;
    let packet = event.packet();

    match packet {
        Some(p) => {
            let packet_data = p.data.as_slice();
            let decoded: Result<CrossChainQuery, DecodeError> = prost::Message::decode(packet_data);
            match decoded {
                Ok(msg) => {
                    if msg.msg_type == "cross_chain_query" {
                        let cross_chain_query_event = IbcEvent::CrossChainQuery(SendPacket {
                            packet: p.to_owned(),
                        });
                        IbcEventWithHeight::new(cross_chain_query_event, height)
                    } else {
                        event_with_height
                    }
                }
                Err(_) => event_with_height,
            }
        }
        None => event_with_height,
    }
}
