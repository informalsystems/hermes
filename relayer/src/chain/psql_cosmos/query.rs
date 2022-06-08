use eyre::WrapErr;
use prost::Message;
//use std::thread;
//use std::time::Duration;
use sqlx::PgPool;
use tendermint::abci::{self, responses::Codespace, tag::Tag, Event, Gas, Info, Log};
use tendermint_proto::abci::TxResult;
use tendermint_rpc::endpoint::tx::Response as ResultTx;
use tendermint_rpc::endpoint::tx_search::Response as TxSearchResponse;
use tracing::{info, trace};

use ibc::core::ics02_client::client_consensus::QueryClientEventRequest;
use ibc::core::ics02_client::events as ClientEvents;
use ibc::core::ics04_channel::channel::QueryPacketEventDataRequest;
use ibc::core::ics04_channel::events as ChannelEvents;
use ibc::core::ics04_channel::packet::{Packet, Sequence};
use ibc::core::ics24_host::identifier::ChainId;
use ibc::events::{from_tx_response_event, IbcEvent};
use ibc::query::QueryTxRequest;
use ibc::Height as ICSHeight;

use crate::error::Error;

/// This function queries transactions for events matching certain criteria.
/// 1. Client Update request - returns a vector with at most one update client event
/// 2. Packet event request - returns at most one packet event for each sequence specified
///    in the request.
///    Note - there is no way to format the packet query such that it asks for Tx-es with either
///    sequence (the query conditions can only be AND-ed).
///    There is a possibility to include "<=" and ">=" conditions but it doesn't work with
///    string attributes (sequence is emmitted as a string).
///    Therefore, for packets we perform one tx_search for each sequence.
///    Alternatively, a single query for all packets could be performed but it would return all
///    packets ever sent.

fn filter_matching_event(
    event: Event,
    request: &QueryPacketEventDataRequest,
    seq: Sequence,
) -> Option<IbcEvent> {
    fn matches_packet(
        request: &QueryPacketEventDataRequest,
        seq: Sequence,
        packet: &Packet,
    ) -> bool {
        packet.source_port == request.source_port_id
            && packet.source_channel == request.source_channel_id
            && packet.destination_port == request.destination_port_id
            && packet.destination_channel == request.destination_channel_id
            && packet.sequence == seq
    }

    if event.type_str != request.event_id.as_str() {
        return None;
    }

    let ibc_event = ChannelEvents::try_from_tx(&event)?;
    match ibc_event {
        IbcEvent::SendPacket(ref send_ev) if matches_packet(request, seq, &send_ev.packet) => {
            Some(ibc_event)
        }
        IbcEvent::WriteAcknowledgement(ref ack_ev)
            if matches_packet(request, seq, &ack_ev.packet) =>
        {
            Some(ibc_event)
        }
        _ => None,
    }
}

pub fn all_ibc_events_from_tx_search_response(
    chain_id: &ChainId,
    height: ICSHeight,
    result: abci::DeliverTx,
) -> Vec<IbcEvent> {
    let mut events = vec![];
    for event in result.events {
        if let Some(ibc_ev) = from_tx_response_event(height, &event) {
            events.push(ibc_ev);
        }
    }
    events
}

fn event_attribute_to_tag(a: tendermint_proto::abci::EventAttribute) -> Result<Tag, Error> {
    let key = String::from_utf8(a.key).unwrap();
    let value = String::from_utf8(a.value).unwrap();

    Ok(Tag {
        key: key.into(),
        value: value.into(),
    })
}

fn proto_to_abci_event(e: tendermint_proto::abci::Event) -> Result<Event, Error> {
    let attributes = e
        .attributes
        .into_iter()
        .filter_map(|a| event_attribute_to_tag(a).ok())
        .collect::<Vec<Tag>>();

    Ok(Event {
        type_str: e.r#type,
        attributes,
    })
}

pub fn proto_to_deliver_tx(
    deliver_tx: tendermint_proto::abci::ResponseDeliverTx,
) -> Result<abci::DeliverTx, Error> {
    let events = deliver_tx
        .events
        .into_iter()
        .filter_map(|r| proto_to_abci_event(r).ok())
        .collect();

    Ok(abci::DeliverTx {
        code: deliver_tx.code.into(),
        data: deliver_tx.data.into(),
        log: Log::new(deliver_tx.log),
        info: Info::new(deliver_tx.info),
        gas_wanted: Gas::from(deliver_tx.gas_wanted as u64),
        gas_used: Gas::from(deliver_tx.gas_used as u64),
        codespace: Codespace::new(deliver_tx.codespace),
        events,
    })
}

#[derive(Debug, sqlx::FromRow)]
struct SqlTxResult {
    tx_hash: String,
    tx_result: Vec<u8>,
}

async fn tx_result_by_hash(pool: &PgPool, hash: &str) -> Result<TxResult, Error> {
    let bytes = sqlx::query_scalar::<_, Vec<u8>>(
        "SELECT tx_result FROM tx_results WHERE tx_hash = $1 LIMIT 1",
    )
    .bind(hash)
    .fetch_one(pool)
    .await
    .map_err(Error::sqlx)?;

    let tx_result = tendermint_proto::abci::TxResult::decode(bytes.as_slice())
        .wrap_err("failed to decode tx result")
        .unwrap();

    Ok(tx_result)
}

async fn tx_result_by_header_fields(
    pool: &PgPool,
    search: &QueryClientEventRequest,
) -> Result<(TxResult, String), Error> {
    let result = sqlx::query_as::<_, SqlTxResult>(
        "SELECT tx_hash, tx_result \
        FROM ibc_tx_client_events WHERE \
        type = $1 and \
        client_id = $2 and \
        consensus_height = $3 \
        LIMIT 1",
    )
    .bind(search.event_id.as_str())
    .bind(search.client_id.as_str())
    .bind(format!("{}", search.consensus_height.revision_height))
    .fetch_one(pool)
    .await
    .map_err(Error::sqlx)?;

    let tx_result = tendermint_proto::abci::TxResult::decode(result.tx_result.as_slice())
        .wrap_err("failed to decode tx result")
        .unwrap();

    Ok((tx_result, result.tx_hash))
}

#[tracing::instrument(skip(pool))]
pub async fn header_search(
    pool: &PgPool,
    search: &QueryClientEventRequest,
) -> Result<TxSearchResponse, Error> {
    info!(
        client_id = %search.client_id,
        consensus_height = %search.consensus_height,
        "got header search"
    );

    let (raw_tx_result, hash) = tx_result_by_header_fields(pool, search).await?;
    let deliver_tx = raw_tx_result.result.unwrap();
    let tx_result = proto_to_deliver_tx(deliver_tx)?;

    trace!(tx_result.events = ? &tx_result.events, "got events");

    let txs = vec![ResultTx {
        hash: hash.parse().unwrap(), // TODO: validate hash earlier
        height: raw_tx_result.height.try_into().unwrap(),
        index: raw_tx_result.index,
        tx_result,
        tx: raw_tx_result.tx.into(),
        proof: None,
    }];

    Ok(TxSearchResponse {
        txs,
        total_count: 1,
    })
}

// Extracts from the Tx the update client event for the requested client and height.
// Note: in the Tx, there may have been multiple events, some of them may be
// for update of other clients that are not relevant to the request.
// For example, if we're querying for a transaction that includes the update for client X at
// consensus height H, it is possible that the transaction also includes an update client
// for client Y at consensus height H'. This is the reason the code iterates all event fields in the
// returned Tx to retrieve the relevant ones.
// Returns `None` if no matching event was found.
fn update_client_from_tx_search_response(
    chain_id: &ChainId,
    request: &QueryClientEventRequest,
    response: ResultTx,
) -> Option<IbcEvent> {
    let height = ICSHeight::new(chain_id.version(), u64::from(response.height));
    if request.height != ICSHeight::zero() && height > request.height {
        return None;
    }

    response
        .tx_result
        .events
        .into_iter()
        .filter(|event| event.type_str == request.event_id.as_str())
        .flat_map(|event| ClientEvents::try_from_tx(&event))
        .flat_map(|event| match event {
            IbcEvent::UpdateClient(mut update) => {
                update.common.height = height;
                Some(update)
            }
            _ => None,
        })
        .find(|update| {
            update.common.client_id == request.client_id
                && update.common.consensus_height == request.consensus_height
        })
        .map(IbcEvent::UpdateClient)
}

async fn tx_result_by_packet_fields(
    pool: &PgPool,
    search: &QueryPacketEventDataRequest,
) -> Result<(TxResult, String), Error> {
    let sequence = search.sequences.first().unwrap();
    let result = sqlx::query_as::<_, SqlTxResult>(
        "SELECT tx_hash, tx_result FROM ibc_tx_packet_events WHERE \
        packet_sequence = $1 and \
        type = $2 and \
        packet_src_channel = $3 and \
        packet_src_port = $4 \
        LIMIT 1",
    )
    .bind(format!("{}", sequence))
    .bind(search.event_id.as_str())
    .bind(search.source_channel_id.to_string())
    .bind(search.source_port_id.to_string())
    .fetch_one(pool)
    .await
    .map_err(Error::sqlx)?;

    let tx_result = tendermint_proto::abci::TxResult::decode(result.tx_result.as_slice())
        .wrap_err("failed to decode tx result")
        .unwrap();

    Ok((tx_result, result.tx_hash))
}

#[tracing::instrument(skip(pool))]
pub async fn packet_search(
    pool: &PgPool,
    search: &QueryPacketEventDataRequest,
) -> Result<TxSearchResponse, Error> {
    info!(seq = ?search.sequences, "got sequence");

    let (raw_tx_result, hash) = tx_result_by_packet_fields(pool, search).await?;
    let deliver_tx = raw_tx_result.result.unwrap();
    let tx_result = proto_to_deliver_tx(deliver_tx)?;

    trace!(tx_result.events = ? &tx_result.events, "got events");

    let txs = vec![ResultTx {
        hash: hash.parse().unwrap(), // TODO: validate hash earlier
        height: raw_tx_result.height.try_into().unwrap(),
        index: raw_tx_result.index,
        tx_result,
        tx: raw_tx_result.tx.into(),
        proof: None,
    }];

    Ok(TxSearchResponse {
        txs,
        total_count: 1,
    })
}

// Extract the packet events from the query_txs RPC response. For any given
// packet query, there is at most one Tx matching such query. Moreover, a Tx may
// contain several events, but a single one must match the packet query.
// For example, if we're querying for the packet with sequence 3 and this packet
// was committed in some Tx along with the packet with sequence 4, the response
// will include both packets. For this reason, we iterate all packets in the Tx,
// searching for those that match (which must be a single one).
fn packet_from_tx_search_response(
    chain_id: &ChainId,
    request: &QueryPacketEventDataRequest,
    seq: Sequence,
    response: ResultTx,
) -> Option<IbcEvent> {
    let height = ICSHeight::new(chain_id.version(), u64::from(response.height));
    if request.height != ICSHeight::zero() && height > request.height {
        return None;
    }

    response
        .tx_result
        .events
        .into_iter()
        .find_map(|ev| filter_matching_event(ev, request, seq))
}

pub async fn query_txs(
    pool: &PgPool,
    chain_id: &ChainId,
    search: &QueryTxRequest,
) -> Result<Vec<IbcEvent>, Error> {
    match search {
        QueryTxRequest::Packet(request) => {
            crate::time!("query_txs: query packet events");

            let mut result: Vec<IbcEvent> = vec![];

            // TODO - make a single psql query
            for seq in &request.sequences {
                let response = packet_search(pool, request).await?;
                // query first (and only) Tx that includes the event specified in the query request

                assert!(
                    response.txs.len() <= 1,
                    "packet_from_tx_search_response: unexpected number of txs"
                );

                if response.txs.is_empty() {
                    continue;
                }

                if let Some(event) =
                    packet_from_tx_search_response(chain_id, request, *seq, response.txs[0].clone())
                {
                    result.push(event);
                }
            }
            Ok(result)
        }

        QueryTxRequest::Client(request) => {
            let mut response = header_search(pool, request).await?;
            if response.txs.is_empty() {
                return Ok(vec![]);
            }

            // the response must include a single Tx as specified in the query.
            assert!(
                response.txs.len() <= 1,
                "client_event_from_tx_search_response: unexpected number of txs"
            );

            let tx = response.txs.remove(0);

            let event = update_client_from_tx_search_response(chain_id, request, tx);

            Ok(event.into_iter().collect())
        }

        QueryTxRequest::Transaction(tx) => {
            let hash = tx.0.to_string();
            let raw_tx_result = tx_result_by_hash(pool, hash.as_str()).await?;
            let height =
                ICSHeight::new(chain_id.version(), raw_tx_result.height.try_into().unwrap());

            let deliver_tx = raw_tx_result.result.unwrap();
            let tx_result = proto_to_deliver_tx(deliver_tx)?;
            if tx_result.code.is_err() {
                return Ok(vec![IbcEvent::ChainError(format!(
                    "deliver_tx for {} reports error: code={:?}, log={:?}",
                    hash, tx_result.code, tx_result.log
                ))]);
            }
            Ok(all_ibc_events_from_tx_search_response(
                chain_id, height, tx_result,
            ))
        }
    }
}
