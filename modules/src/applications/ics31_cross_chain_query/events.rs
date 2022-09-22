use crate::applications::ics31_cross_chain_query::error::Error;
use crate::applications::ics31_cross_chain_query::packet::CrossChainQueryPacket;
use crate::events::IbcEventType;
use crate::prelude::*;
use core::fmt::{Display, Formatter};
use core::str::FromStr;
use serde::Serialize;
use tendermint::abci::tag::{Key, Tag, Value};
use tendermint::abci::Event as AbciEvent;

/// Types for the IBC events emitted from Tendermint Websocket by the cross-chain-query module.

pub const ATTRIBUTE_TIMEOUT_HEIGHT_KEY: &str = "query_timeout_height";
pub const ATTRIBUTE_TIMEOUT_TIMESTAMP_KEY: &str = "query_timeout_timestamp";
pub const ATTRIBUTE_QUERY_HEIGHT_KEY: &str = "query_height";
pub const ATTRIBUTE_QUERY_ID_KEY: &str = "query_id";
pub const ATTRIBUTE_QUERY_PATH_KEY: &str = "query_path";

#[derive(Serialize, Clone, Debug, PartialEq, Eq)]
pub struct SendPacket {
    pub packet: CrossChainQueryPacket,
}

impl SendPacket {
    pub fn new(
        id: String,
        path: String,
        height: String,
        timeout_height: String,
        timeout_timestamp: String,
    ) -> SendPacket {
        Self {
            packet: CrossChainQueryPacket {
                id,
                path,
                height,
                timeout_height,
                timeout_timestamp,
            },
        }
    }

    pub fn from_packet(packet: CrossChainQueryPacket) -> SendPacket {
        Self { packet }
    }
}

impl Display for SendPacket {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.packet)
    }
}

impl TryFrom<SendPacket> for AbciEvent {
    type Error = Error;

    fn try_from(value: SendPacket) -> Result<Self, Self::Error> {
        Ok(AbciEvent {
            type_str: IbcEventType::CrossChainQuery.as_str().to_string(),
            attributes: vec![
                Tag {
                    key: Key::from_str(ATTRIBUTE_QUERY_ID_KEY).unwrap(),
                    value: Value::from_str(&value.packet.id).unwrap(),
                },
                Tag {
                    key: Key::from_str(ATTRIBUTE_QUERY_PATH_KEY).unwrap(),
                    value: Value::from_str(&value.packet.path).unwrap(),
                },
                Tag {
                    key: Key::from_str(ATTRIBUTE_QUERY_HEIGHT_KEY).unwrap(),
                    value: Value::from_str(&value.packet.height).unwrap(),
                },
                Tag {
                    key: Key::from_str(ATTRIBUTE_TIMEOUT_HEIGHT_KEY).unwrap(),
                    value: Value::from_str(&value.packet.timeout_height).unwrap(),
                },
                Tag {
                    key: Key::from_str(ATTRIBUTE_TIMEOUT_TIMESTAMP_KEY).unwrap(),
                    value: Value::from_str(&value.packet.timeout_timestamp).unwrap(),
                },
            ],
        })
    }
}
