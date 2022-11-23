use crate::prelude::*;
use crate::core::ics24_host::identifier::{ChainId, ConnectionId};

use super::error::Error;

use core::str::FromStr;
use serde::{Serialize, Deserialize};
use tendermint::block::Height;
use tendermint_rpc::abci::{Event as AbciEvent, Path as TendermintPath};
use tendermint_rpc::abci::tag::Tag;


#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct CrossChainQueryPacket {
    pub module: String,
    pub action: String,
    pub query_id: String,
    pub chain_id: ChainId,
    pub connection_id: ConnectionId,
    pub query_type: TendermintPath,
    pub height: Height,
    pub request: String,
}

fn find_value(key: &str, entries: &[Tag]) -> Result<String, Error> {
    entries
        .iter()
        .find_map(|entry| {
            if entry.key.as_ref() == key {
                Some(entry.value.to_string())
            } else {
                None
            }
        })
        .ok_or_else(|| Error::attribute(key.to_string()))
}

fn new_tag(key: &str, value: &str) -> Tag {
    Tag {
        key: key.parse().unwrap(),
        value: value.parse().unwrap(),
    }
}

impl From<CrossChainQueryPacket> for AbciEvent {
    fn from(packet: CrossChainQueryPacket) -> Self {
        let attributes: Vec<Tag> = vec![
            new_tag("module", packet.module.as_str()),
            new_tag("action", packet.action.as_str()),
            new_tag("query_id", packet.query_id.as_str()),
            new_tag("chain_id", packet.chain_id.as_str()),
            new_tag("connection_id", packet.connection_id.as_str()),
            new_tag("type", &packet.query_type.to_string()),
            new_tag("request", packet.request.as_str()),
            new_tag("height", &packet.height.to_string()),
        ];

        AbciEvent {
            type_str: String::from("message"),
            attributes,
        }
    }
}

impl<'a> TryFrom<&'a Vec<Tag>> for CrossChainQueryPacket {
    type Error = Error;

    fn try_from(entries: &'a Vec<Tag>) -> Result<Self, Self::Error> {
        let module = find_value("module", &entries)?;
        let action = find_value("action", &entries)?;
        let query_id = find_value("query_id", &entries)?;
        let chain_id_str = find_value("chain_id", &entries)?;
        let connection_id_str = find_value("connection_id", &entries)?;
        let query_type_str = find_value("type", &entries)?;
        let request = find_value("request", &entries)?;
        let height_str = find_value("height", &entries)?;

        let chain_id = ChainId::from_string(&chain_id_str);
        let connection_id = ConnectionId::from_str(&connection_id_str).map_err(|_| Error::ics24())?;
        let query_path = TendermintPath::from_str(&query_type_str).map_err(|_| Error::tendermint())?;
        let height = Height::from_str(&height_str).map_err(|_| Error::tendermint())?;

        Ok(
            Self {
                module,
                action,
                query_id,
                chain_id,
                connection_id,
                query_type: query_path,
                height,
                request,
            }
        )
    }
}