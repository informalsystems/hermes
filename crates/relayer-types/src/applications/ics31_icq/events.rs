use crate::core::ics24_host::identifier::{ChainId, ConnectionId};
use crate::events::IbcEvent;
use crate::prelude::*;

use super::error::Error;

use core::str::FromStr;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use tendermint::{abci, block::Height};
const EVENT_TYPE_PREFIX: &str = "query_request";

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct CrossChainQueryPacket {
    pub module: String,
    pub action: String,
    pub query_id: String,
    pub chain_id: ChainId,
    pub connection_id: ConnectionId,
    pub query_type: String,
    pub height: Height,
    pub request: String,
}

fn find_value<'a>(key: &str, entries: &'a [abci::EventAttribute]) -> Result<&'a str, Error> {
    entries
        .iter()
        .find_map(|entry| {
            if entry.key == key {
                Some(entry.value.as_str())
            } else {
                None
            }
        })
        .ok_or_else(|| Error::event(format!("attribute not found for key: {key}")))
}

fn new_attr(key: &str, value: &str) -> abci::EventAttribute {
    abci::EventAttribute {
        key: String::from(key),
        value: String::from(value),
        index: true,
    }
}

impl From<CrossChainQueryPacket> for abci::Event {
    fn from(packet: CrossChainQueryPacket) -> Self {
        let attributes: Vec<abci::EventAttribute> = vec![
            new_attr("module", packet.module.as_str()),
            new_attr("action", packet.action.as_str()),
            new_attr("query_id", packet.query_id.as_str()),
            new_attr("chain_id", packet.chain_id.as_str()),
            new_attr("connection_id", packet.connection_id.as_str()),
            new_attr("type", &packet.query_type.to_string()),
            new_attr("request", packet.request.as_str()),
            new_attr("height", &packet.height.to_string()),
        ];

        abci::Event {
            kind: String::from("message"),
            attributes,
        }
    }
}

impl<'a> TryFrom<&'a [abci::EventAttribute]> for CrossChainQueryPacket {
    type Error = Error;

    fn try_from(entries: &'a [abci::EventAttribute]) -> Result<Self, Error> {
        let module = find_value("module", entries)?.to_string();
        let action = find_value("action", entries)?.to_string();
        let query_id = find_value("query_id", entries)?.to_string();
        let chain_id_str = find_value("chain_id", entries)?;
        let connection_id_str = find_value("connection_id", entries)?;
        let query_type = find_value("type", entries)?.to_string();
        let request = find_value("request", entries)?.to_string();
        let height_str = find_value("height", entries)?;

        let chain_id = ChainId::from_string(chain_id_str);
        let connection_id = ConnectionId::from_str(connection_id_str)?;
        let height = Height::from_str(height_str)?;

        Ok(Self {
            module,
            action,
            query_id,
            chain_id,
            connection_id,
            query_type,
            height,
            request,
        })
    }
}

fn fetch_first_element_from_events(
    block_events: &BTreeMap<String, Vec<String>>,
    key: &str,
) -> Result<String, Error> {
    let res = block_events
        .get(key)
        .ok_or_else(|| Error::event(format!("attribute not found for key: {key}")))?
        .get(0)
        .ok_or_else(|| {
            Error::event(format!(
                "element at position 0, of attribute with key `{key}`, not found"
            ))
        })?;

    Ok(res.clone())
}

impl CrossChainQueryPacket {
    pub fn extract_query_event(
        block_events: &BTreeMap<String, Vec<String>>,
    ) -> Result<IbcEvent, Error> {
        let chain_id_str = fetch_first_element_from_events(
            block_events,
            &format!("{}.{}", EVENT_TYPE_PREFIX, "chain_id"),
        )?;
        let connection_id_str = fetch_first_element_from_events(
            block_events,
            &format!("{}.{}", EVENT_TYPE_PREFIX, "connection_id"),
        )?;
        let query_type = fetch_first_element_from_events(
            block_events,
            &format!("{}.{}", EVENT_TYPE_PREFIX, "type"),
        )?;
        let height_str = fetch_first_element_from_events(
            block_events,
            &format!("{}.{}", EVENT_TYPE_PREFIX, "height"),
        )?;

        Ok(IbcEvent::CrossChainQueryPacket(CrossChainQueryPacket {
            module: fetch_first_element_from_events(
                block_events,
                &format!("{}.{}", EVENT_TYPE_PREFIX, "module"),
            )?,
            action: fetch_first_element_from_events(
                block_events,
                &format!("{}.{}", EVENT_TYPE_PREFIX, "action"),
            )?,
            query_id: fetch_first_element_from_events(
                block_events,
                &format!("{}.{}", EVENT_TYPE_PREFIX, "query_id"),
            )?,
            chain_id: ChainId::from_string(&chain_id_str),
            connection_id: ConnectionId::from_str(&connection_id_str)?,
            query_type,
            height: Height::from_str(&height_str)?,
            request: fetch_first_element_from_events(
                block_events,
                &format!("{}.{}", EVENT_TYPE_PREFIX, "request"),
            )?,
        }))
    }
}
