use std::collections::BTreeMap;
use std::str::FromStr;

use serde::{Deserialize, Serialize};
use tendermint::{abci, block::Height};

use crate::core::ics24_host::identifier::{ChainId, ConnectionId};
use crate::events::IbcEvent;

use super::error::Error;

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

fn fetch_nth_element_from_events<'a>(
    block_events: &'a BTreeMap<String, Vec<String>>,
    key: &str,
    index: usize,
) -> Result<&'a String, Error> {
    let res = block_events
        .get(key)
        .ok_or_else(|| Error::event(format!("attribute not found for key: {key}")))?
        .get(index)
        .ok_or_else(|| {
            Error::event(format!(
                "element at position {index}, of attribute with key `{key}`, not found"
            ))
        })?;

    Ok(res)
}

impl CrossChainQueryPacket {
    pub fn extract_query_events(
        block_events: &BTreeMap<String, Vec<String>>,
    ) -> Result<Vec<IbcEvent>, Error> {
        let events_count = block_events
            .get(&format!("{}.{}", EVENT_TYPE_PREFIX, "query_id"))
            .ok_or_else(|| Error::event("attribute not found for key: query_id".to_string()))?
            .len();

        let cross_chain_queries = (0..events_count)
            .filter_map(|index| Self::extract_nth_query_event(block_events, index).ok())
            .collect::<Vec<_>>();

        Ok(cross_chain_queries)
    }

    fn extract_nth_query_event(
        block_events: &BTreeMap<String, Vec<String>>,
        index: usize,
    ) -> Result<IbcEvent, Error> {
        let chain_id_str = fetch_nth_element_from_events(
            block_events,
            &format!("{}.{}", EVENT_TYPE_PREFIX, "chain_id"),
            index,
        )?;
        let connection_id_str = fetch_nth_element_from_events(
            block_events,
            &format!("{}.{}", EVENT_TYPE_PREFIX, "connection_id"),
            index,
        )?;
        let height_str = fetch_nth_element_from_events(
            block_events,
            &format!("{}.{}", EVENT_TYPE_PREFIX, "height"),
            index,
        )?;
        let query_type = fetch_nth_element_from_events(
            block_events,
            &format!("{}.{}", EVENT_TYPE_PREFIX, "type"),
            index,
        )?;
        let query_id = fetch_nth_element_from_events(
            block_events,
            &format!("{}.{}", EVENT_TYPE_PREFIX, "query_id"),
            index,
        )?;
        let module = fetch_nth_element_from_events(
            block_events,
            &format!("{}.{}", EVENT_TYPE_PREFIX, "module"),
            index,
        )?;
        let action = fetch_nth_element_from_events(
            block_events,
            &format!("{}.{}", EVENT_TYPE_PREFIX, "action"),
            index,
        )?;
        let request = fetch_nth_element_from_events(
            block_events,
            &format!("{}.{}", EVENT_TYPE_PREFIX, "request"),
            index,
        )?;

        Ok(IbcEvent::CrossChainQueryPacket(CrossChainQueryPacket {
            module: module.clone(),
            action: action.clone(),
            query_id: query_id.clone(),
            chain_id: ChainId::from_string(chain_id_str),
            connection_id: ConnectionId::from_str(connection_id_str)?,
            query_type: query_type.clone(),
            height: Height::from_str(height_str)?,
            request: request.clone(),
        }))
    }
}
