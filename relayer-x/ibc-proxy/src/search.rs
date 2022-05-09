use color_eyre::eyre::{eyre, Context};
use tendermint_rpc::query::{Condition, Operand, Query};
use tracing::info;

use crate::{error::ReportError, jsonrpc::JsonRpc, types::TxSearchRequest};

#[derive(Clone, Debug)]
pub enum Search {
    Tx(TxSearch),
    Packet(PacketSearch),
    Header(HeaderSearch),
}

#[derive(Clone, Debug)]
pub struct TxSearch {
    pub hash: String,
}

#[derive(Clone, Debug)]
pub struct HeaderSearch {
    pub client_id: String,
    pub consensus_height: String,
}

#[derive(Clone, Debug)]
pub struct PacketSearch {
    pub packet_src_channel: String,
    pub packet_src_port: String,
    pub packet_dst_channel: String,
    pub packet_dst_port: String,
    pub packet_sequence: String,
}

impl Search {
    pub fn from_json_rpc(body: &JsonRpc<serde_json::Value>) -> Result<Search, ReportError> {
        if body.method != "tx_search" {
            return Err(eyre!("not a tx search request").into());
        }

        let request = serde_json::from_value::<TxSearchRequest>(body.params.clone())
            .wrap_err("invalid tx search request")?;

        info!(query = ?request.query, "Query");

        let query: Query = request.query.parse().wrap_err("failed to parse query")?;

        let request = Self::from_query(&query)
            .ok_or_else(|| eyre!("failed to extract request from query"))?;

        Ok(request)
    }

    pub fn from_query(query: &Query) -> Option<Self> {
        parse_tx_query(query)
            .map(Self::Tx)
            .or_else(|| parse_packet_query(query).map(Self::Packet))
            .or_else(|| parse_header_query(query).map(Self::Header))
    }
}

fn parse_tx_query(query: &Query) -> Option<TxSearch> {
    let hash = find_by_key(query, |k| k == "tx.hash")?;
    Some(TxSearch { hash })
}

fn parse_packet_query(query: &Query) -> Option<PacketSearch> {
    let packet_src_channel = find_by_key(query, |k| k.ends_with(".packet_src_channel"))?;
    let packet_src_port = find_by_key(query, |k| k.ends_with(".packet_src_port"))?;
    let packet_dst_channel = find_by_key(query, |k| k.ends_with(".packet_dst_channel"))?;
    let packet_dst_port = find_by_key(query, |k| k.ends_with(".packet_dst_port"))?;
    let packet_sequence = find_by_key(query, |k| k.ends_with(".packet_sequence"))?;

    Some(PacketSearch {
        packet_src_channel,
        packet_src_port,
        packet_dst_channel,
        packet_dst_port,
        packet_sequence,
    })
}

fn parse_header_query(query: &Query) -> Option<HeaderSearch> {
    let client_id = find_by_key(query, |k| k.ends_with(".client_id"))?;
    let consensus_height = find_by_key(query, |k| k.ends_with(".consensus_height"))?;

    Some(HeaderSearch {
        client_id,
        consensus_height,
    })
}

fn find_by_key(query: &Query, pred: impl Fn(&str) -> bool) -> Option<String> {
    query.conditions.iter().find_map(|c| match c {
        Condition::Eq(key, Operand::String(value)) if pred(key) => Some(value.to_owned()),
        _ => None,
    })
}
