use eyre::WrapErr;
use prost::Message;
use sqlx::{types::Json, PgPool};

use tendermint::abci::transaction::Hash;
use tendermint::abci::{self, responses::Codespace, tag::Tag, Event, Gas, Info, Log};
use tendermint_proto::abci::TxResult;
use tendermint_rpc::endpoint::tx::Response as ResultTx;
use tendermint_rpc::endpoint::tx_search::Response as TxSearchResponse;
use tracing::{info, trace};

use ibc::core::ics02_client::events as ClientEvents;
use ibc::core::ics02_client::height::Height;
use ibc::core::ics03_connection::connection::IdentifiedConnectionEnd;
use ibc::core::ics04_channel::channel::IdentifiedChannelEnd;
use ibc::core::ics04_channel::events as ChannelEvents;
use ibc::core::ics04_channel::packet::{parse_timeout_height, Packet};
use ibc::core::ics24_host::identifier::{ChainId, ChannelId, ConnectionId};
use ibc::events::{self, from_tx_response_event, IbcEvent, WithBlockDataType};
use ibc::Height as ICSHeight;

use crate::chain::cosmos::types::tx::{TxStatus, TxSyncResult};
use crate::chain::endpoint::ChainStatus;
use crate::chain::psql_cosmos::update::{IbcData, IbcSnapshot, PacketId};
use crate::chain::requests::{
    QueryBlockRequest, QueryClientEventRequest, QueryHeight, QueryPacketEventDataRequest,
    QueryTxRequest,
};
use crate::error::Error;

/// This function queries transactions for events matching certain criteria.
/// 1. Client Update request - returns a vector with at most one update client event
/// 2. Packet event request - returns at most one packet event for each sequence specified
///    in the request.
fn filter_matching_event(event: Event, request: &QueryPacketEventDataRequest) -> Option<IbcEvent> {
    fn matches_packet(request: &QueryPacketEventDataRequest, packet: &Packet) -> bool {
        packet.source_port == request.source_port_id
            && packet.source_channel == request.source_channel_id
            && packet.destination_port == request.destination_port_id
            && packet.destination_channel == request.destination_channel_id
            && request.sequences.contains(&packet.sequence)
    }

    if event.type_str != request.event_id.as_str() {
        return None;
    }

    let ibc_event = ChannelEvents::try_from_tx(&event)?;
    match ibc_event {
        IbcEvent::SendPacket(ref send_ev) if matches_packet(request, &send_ev.packet) => {
            Some(ibc_event)
        }
        IbcEvent::WriteAcknowledgement(ref ack_ev) if matches_packet(request, &ack_ev.packet) => {
            Some(ibc_event)
        }
        _ => None,
    }
}

pub fn all_ibc_events_from_tx_search_response(
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
    .bind(format!("{}", search.consensus_height.revision_height()))
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
fn update_client_events_from_tx_search_response(
    chain_id: &ChainId,
    request: &QueryClientEventRequest,
    response: ResultTx,
) -> Option<IbcEvent> {
    let height = ICSHeight::new(chain_id.version(), u64::from(response.height)).unwrap();
    if let QueryHeight::Specific(query_height) = request.query_height {
        if height > query_height {
            return None;
        }
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

async fn tx_results_by_packet_fields(
    pool: &PgPool,
    search: &QueryPacketEventDataRequest,
) -> Result<Vec<(i64, TxResult, String)>, Error> {
    // Convert from `[Sequence(1), Sequence(2)]` to String `"('1', '2')"`
    let seqs = search
        .clone()
        .sequences
        .into_iter()
        .map(|i| format!("'{}'", i))
        .collect::<Vec<String>>();
    let seqs_string = format!("({})", seqs.join(", "));

    let sql_select_string = format!(
        "SELECT DISTINCT tx_hash, tx_result FROM ibc_tx_packet_events WHERE \
        packet_sequence IN {} and \
        type = $1 and \
        packet_src_channel = $2 and \
        packet_src_port = $3",
        seqs_string
    );

    let results = sqlx::query_as::<_, SqlTxResult>(sql_select_string.as_str())
        .bind(search.event_id.as_str())
        .bind(search.source_channel_id.to_string())
        .bind(search.source_port_id.to_string())
        .fetch_all(pool)
        .await
        .map_err(Error::sqlx)?;

    let tx_result = results
        .into_iter()
        .map(|result| {
            let tx_res = tendermint_proto::abci::TxResult::decode(result.tx_result.as_slice())
                .wrap_err("failed to decode tx result")
                .unwrap();
            (tx_res.height, tx_res, result.tx_hash)
        })
        .collect();

    Ok(tx_result)
}

#[tracing::instrument(skip(pool))]
pub async fn tx_search_response_from_packet_query(
    pool: &PgPool,
    search: &QueryPacketEventDataRequest,
) -> Result<TxSearchResponse, Error> {
    trace!("tx_search_response_from_packet_query");

    let results = tx_results_by_packet_fields(pool, search).await?;
    let total_count = results.len() as u32;

    let txs = results
        .into_iter()
        .map(|result| {
            let (height, raw_tx_result, hash) = result;
            let deliver_tx = raw_tx_result.result.unwrap();
            trace!(tx_result.events = ? &deliver_tx.events, "got events");

            let tx_result = proto_to_deliver_tx(deliver_tx).unwrap();

            ResultTx {
                hash: hash.parse().unwrap(),
                height: height.try_into().unwrap(),
                index: raw_tx_result.index,
                tx_result,
                tx: raw_tx_result.tx.into(),
                proof: None,
            }
        })
        .collect();

    Ok(TxSearchResponse { txs, total_count })
}

// Extract the packet events from the query_txs RPC responses.
fn packet_events_from_tx_search_response(
    chain_id: &ChainId,
    request: &QueryPacketEventDataRequest,
    responses: Vec<ResultTx>,
) -> Vec<IbcEvent> {
    let mut events = vec![];
    for response in responses {
        let height = ICSHeight::new(chain_id.version(), u64::from(response.height)).unwrap();
        if let QueryHeight::Specific(specific_query_height) = request.height {
            if height > specific_query_height {
                continue;
            }
        };

        let mut new_events = response
            .tx_result
            .events
            .into_iter()
            .filter_map(|ev| filter_matching_event(ev, request))
            .collect::<Vec<_>>();

        events.append(&mut new_events)
    }
    events
}

pub async fn query_txs_from_tendermint(
    pool: &PgPool,
    chain_id: &ChainId,
    search: &QueryTxRequest,
) -> Result<Vec<IbcEvent>, Error> {
    match search {
        QueryTxRequest::Packet(request) => {
            crate::time!("query_txs_from_tendermint: query packet events");

            let responses = tx_search_response_from_packet_query(pool, request).await?;
            let events = packet_events_from_tx_search_response(chain_id, request, responses.txs);
            Ok(events)
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

            let event = update_client_events_from_tx_search_response(chain_id, request, tx);

            Ok(event.into_iter().collect())
        }

        QueryTxRequest::Transaction(tx) => {
            let hash = tx.0.to_string();
            let raw_tx_result = tx_result_by_hash(pool, hash.as_str()).await?;
            let height =
                ICSHeight::new(chain_id.version(), raw_tx_result.height.try_into().unwrap())
                    .unwrap();

            let deliver_tx = raw_tx_result.result.unwrap();
            let tx_result = proto_to_deliver_tx(deliver_tx)?;
            if tx_result.code.is_err() {
                return Ok(vec![IbcEvent::ChainError(format!(
                    "deliver_tx for {} reports error: code={:?}, log={:?}",
                    hash, tx_result.code, tx_result.log
                ))]);
            }
            Ok(all_ibc_events_from_tx_search_response(height, tx_result))
        }
    }
}

pub async fn query_txs_from_ibc_snapshots(
    pool: &PgPool,
    chain_id: &ChainId,
    search: &QueryTxRequest,
) -> Result<Vec<IbcEvent>, Error> {
    match search {
        QueryTxRequest::Packet(request) => {
            crate::time!("query_txs_from_ibc_snapshots: query packet events");
            match request.event_id {
                WithBlockDataType::SendPacket => {
                    let (height, all_packets) = query_sent_packets(pool, &request.height).await?;
                    let events = all_packets
                        .into_iter()
                        .filter_map(|packet| {
                            if packet.source_port == request.source_port_id
                                && packet.source_channel == request.source_channel_id
                                && request.sequences.contains(&packet.sequence)
                            {
                                Some(IbcEvent::SendPacket(ChannelEvents::SendPacket {
                                    height,
                                    packet,
                                }))
                            } else {
                                None
                            }
                        })
                        .collect();
                    Ok(events)
                }
                _ => query_txs_from_tendermint(pool, chain_id, search).await,
            }
        }
        _ => query_txs_from_tendermint(pool, chain_id, search).await,
    }
}

async fn abci_tx_results_by_hashes(
    pool: &PgPool,
    hashes: Vec<Hash>,
) -> Result<Vec<(i64, TxResult, String)>, Error> {
    // Convert from `[Sequence(1), Sequence(2)]` to String `"('1', '2')"`
    let hash_string = hashes
        .into_iter()
        .map(|i| format!("'{}'", i))
        .collect::<Vec<String>>();
    let hashes_psql = format!("({})", hash_string.join(", "));
    let sql_select_string = format!(
        "SELECT DISTINCT tx_hash, tx_result FROM tx_results WHERE \
        tx_hash IN {}",
        hashes_psql
    );

    let results = sqlx::query_as::<_, SqlTxResult>(sql_select_string.as_str())
        .fetch_all(pool)
        .await
        .map_err(Error::sqlx)?;

    let tx_result = results
        .into_iter()
        .map(|result| {
            let tx_res = tendermint_proto::abci::TxResult::decode(result.tx_result.as_slice())
                .wrap_err("failed to decode tx result")
                .unwrap();
            (tx_res.height, tx_res, result.tx_hash)
        })
        .collect();

    Ok(tx_result)
}

async fn rpc_tx_results_by_hashes(
    pool: &PgPool,
    hashes: Vec<Hash>,
) -> Result<TxSearchResponse, Error> {
    trace!("search_pending_txs_by_hashes {:?}", hashes);

    let results = abci_tx_results_by_hashes(pool, hashes).await?;
    let total_count = results.len() as u32;

    let txs = results
        .into_iter()
        .map(|result| {
            let (height, raw_tx_result, hash) = result;
            let deliver_tx = raw_tx_result.result.unwrap();
            trace!(tx_result.events = ? &deliver_tx.events, "got events");

            let tx_result = proto_to_deliver_tx(deliver_tx).unwrap();

            ResultTx {
                hash: hash.parse().unwrap(),
                height: height.try_into().unwrap(),
                index: raw_tx_result.index,
                tx_result,
                tx: raw_tx_result.tx.into(),
                proof: None,
            }
        })
        .collect();

    Ok(TxSearchResponse { txs, total_count })
}

fn all_ibc_events_from_tx_result_batch(
    chain_id: &ChainId,
    responses: Vec<ResultTx>,
) -> Vec<Vec<IbcEvent>> {
    let mut events: Vec<Vec<IbcEvent>> = vec![];
    for response in responses {
        let height = ICSHeight::new(chain_id.version(), u64::from(response.height)).unwrap();

        let new_events = if response.tx_result.code.is_err() {
            vec![IbcEvent::ChainError(format!(
                "deliver_tx on chain {} for Tx hash {} reports error: code={:?}, log={:?}",
                chain_id, response.hash, response.tx_result.code, response.tx_result.log
            ))]
        } else {
            response
                .tx_result
                .events
                .into_iter()
                .filter_map(|ev| from_tx_response_event(height, &ev))
                .collect::<Vec<_>>()
        };
        events.push(new_events)
    }
    events
}

pub async fn query_hashes_and_update_tx_sync_events(
    pool: &PgPool,
    chain_id: &ChainId,
    tx_sync_results: &mut [TxSyncResult],
) -> Result<(), Error> {
    // get the hashes of the transactions for which events have not been retrieved yet
    let unsolved_hashes = tx_sync_results
        .iter_mut()
        .filter(|result| matches!(result.status, TxStatus::Pending { .. }))
        .map(|res| res.response.hash)
        .collect();

    // query the chain with all unsolved hashes
    let responses = rpc_tx_results_by_hashes(pool, unsolved_hashes).await?;

    // get the hashes for found transactions
    let solved_hashes = responses
        .txs
        .iter()
        .map(|res| res.hash)
        .collect::<Vec<Hash>>();

    if solved_hashes.is_empty() {
        return Ok(());
    }

    // extract the IBC events from all transactions that were solved
    let solved_txs_events = all_ibc_events_from_tx_result_batch(chain_id, responses.txs);

    // get the pending results for the solved transactions where the results should be stored
    let mut solved_results = tx_sync_results
        .iter_mut()
        .filter(|result| solved_hashes.contains(&result.response.hash))
        .collect::<Vec<&mut TxSyncResult>>();

    for (tx_sync_result, events) in solved_results.iter_mut().zip(solved_txs_events.iter()) {
        // Transaction was included in a block. Check if it was an error.
        let tx_chain_error = events
            .iter()
            .find(|event| matches!(event, IbcEvent::ChainError(_)));

        if let Some(err) = tx_chain_error {
            // Save the error for all messages in the transaction
            let err_events = tx_sync_result
                .events
                .iter()
                .map(|_| err.clone())
                .collect::<Vec<IbcEvent>>();
            tx_sync_result.events = err_events.clone();
        } else {
            tx_sync_result.events = events.clone();
        }
        tx_sync_result.status = TxStatus::ReceivedResponse;
    }
    Ok(())
}

pub async fn query_hashes_and_update_tx_sync_results(
    pool: &PgPool,
    chain_id: &ChainId,
    tx_sync_results: &mut [TxSyncResult],
) -> Result<(), Error> {
    for result in tx_sync_results.iter_mut() {
        if result.response.code.is_err() {
            result.events = vec![IbcEvent::ChainError(format!(
                "check_tx (broadcast_tx_sync) on chain {} for Tx hash {} reports error: code={:?}, log={:?}",
                chain_id, result.response.hash, result.response.code, result.response.log)); result.events.len()]
        }
    }

    query_hashes_and_update_tx_sync_events(pool, chain_id, tx_sync_results).await
}

#[derive(Debug, sqlx::FromRow)]
struct SqlPacketBlockEvents {
    block_id: i64,
    r#type: String,
    packet_src_port: String,
    packet_sequence: String,
    packet_dst_port: String,
    packet_dst_channel: String,
    packet_src_channel: String,
    packet_timeout_height: String,
    packet_timeout_timestamp: String,
    packet_data: String,
    packet_ack: String,
}

async fn block_results_by_packet_fields(
    pool: &PgPool,
    search: &QueryPacketEventDataRequest,
) -> Result<Vec<SqlPacketBlockEvents>, Error> {
    // Convert from `[Sequence(1), Sequence(2)]` to String `"('1', '2')"`
    let seqs = search
        .clone()
        .sequences
        .into_iter()
        .map(|i| format!("'{}'", i))
        .collect::<Vec<String>>();
    let seqs_string = format!("({})", seqs.join(", "));

    let sql_select_string = format!(
        "SELECT DISTINCT * FROM ibc_block_events WHERE \
        packet_sequence IN {} and \
        type = $1 and \
        packet_src_channel = $2 and \
        packet_src_port = $3",
        seqs_string
    );

    let results = sqlx::query_as::<_, SqlPacketBlockEvents>(sql_select_string.as_str())
        .bind(search.event_id.as_str())
        .bind(search.source_channel_id.to_string())
        .bind(search.source_port_id.to_string())
        .fetch_all(pool)
        .await
        .map_err(Error::sqlx)?;

    Ok(results)
}

pub async fn query_blocks(
    pool: &PgPool,
    chain_id: &ChainId,
    search: &QueryBlockRequest,
) -> Result<Vec<IbcEvent>, Error> {
    match search {
        QueryBlockRequest::Packet(request) => {
            crate::time!("query_blocks: query packet events");

            Ok(block_search_response_from_packet_query(pool, chain_id, request).await?)
        }
    }
}

fn ibc_packet_event_from_sql_block_query(
    chain_id: &ChainId,
    event: &SqlPacketBlockEvents,
) -> Option<IbcEvent> {
    fn ibc_packet_from_sql_block_by_packet_query(event: &SqlPacketBlockEvents) -> Packet {
        Packet {
            sequence: event.packet_sequence.parse().unwrap(),
            source_port: event.packet_src_port.parse().unwrap(),
            source_channel: event.packet_src_channel.parse().unwrap(),
            destination_port: event.packet_dst_port.parse().unwrap(),
            destination_channel: event.packet_dst_channel.parse().unwrap(),
            data: Vec::from(event.packet_data.as_bytes()),
            timeout_height: parse_timeout_height(&event.packet_timeout_height).unwrap(),
            timeout_timestamp: event.packet_timeout_timestamp.parse().unwrap(),
        }
    }

    match event.r#type.as_str() {
        events::SEND_PACKET_EVENT => {
            Some(IbcEvent::SendPacket(ChannelEvents::SendPacket {
                height: ICSHeight::new(
                    ChainId::chain_version(chain_id.to_string().as_str()),
                    event.block_id as u64, // TODO - get the height for the block with block_id
                )
                .unwrap(),
                packet: ibc_packet_from_sql_block_by_packet_query(event),
            }))
        }
        events::WRITE_ACK_EVENT => {
            Some(IbcEvent::WriteAcknowledgement(
                ChannelEvents::WriteAcknowledgement {
                    height: ICSHeight::new(
                        ChainId::chain_version(chain_id.to_string().as_str()),
                        event.block_id as u64, // TODO - get the height for the block with block_id
                    )
                    .unwrap(),
                    packet: ibc_packet_from_sql_block_by_packet_query(event),
                    ack: Vec::from(event.packet_ack.as_bytes()),
                },
            ))
        }
        _ => None,
    }
}

#[tracing::instrument(skip(pool))]
pub async fn block_search_response_from_packet_query(
    pool: &PgPool,
    chain_id: &ChainId,
    search: &QueryPacketEventDataRequest,
) -> Result<Vec<IbcEvent>, Error> {
    trace!("block_search_response_from_packet_query");

    let results = block_results_by_packet_fields(pool, search).await?;
    let total_count = results.len() as u32;

    let events = results
        .into_iter()
        .filter_map(|result| ibc_packet_event_from_sql_block_query(chain_id, &result))
        .collect();

    Ok(events)
}

// TODO to get rid of this struct??
// impl FromRow for IbcSnapshot
#[derive(Debug, sqlx::FromRow)]
pub struct IbcSnapshotJson {
    pub height: f64,
    pub json_data: Json<IbcData>,
}

pub async fn query_ibc_data_json(
    pool: &PgPool,
    query_height: &QueryHeight,
) -> Result<IbcSnapshotJson, Error> {
    let sql_select_string = match query_height {
        QueryHeight::Latest => "SELECT * FROM ibc_json ORDER BY height DESC LIMIT 1".to_string(),
        QueryHeight::Specific(h) => format!(
            "SELECT * FROM ibc_json WHERE height = {} LIMIT 1",
            h.revision_height()
        ),
    };

    sqlx::query_as::<_, IbcSnapshotJson>(sql_select_string.as_str())
        .fetch_one(pool)
        .await
        .map_err(Error::sqlx)
}

pub async fn query_ibc_data(
    pool: &PgPool,
    query_height: &QueryHeight,
) -> Result<IbcSnapshot, Error> {
    let result = query_ibc_data_json(pool, query_height).await?;

    let response = IbcSnapshot {
        height: result.height as u64,
        json_data: IbcData {
            app_status: result.json_data.app_status.clone(),
            connections: result.json_data.connections.clone(),
            channels: result.json_data.channels.clone(),
            pending_sent_packets: result.json_data.pending_sent_packets.clone(),
        },
    };
    Ok(response)
}

pub async fn query_application_status(pool: &PgPool) -> Result<ChainStatus, Error> {
    let result = query_ibc_data(pool, &QueryHeight::Latest).await?;
    Ok(result.json_data.app_status)
}

pub async fn query_connections(
    pool: &PgPool,
    query_height: &QueryHeight,
) -> Result<Vec<IdentifiedConnectionEnd>, Error> {
    let result = query_ibc_data(pool, query_height).await?;
    Ok(result.json_data.connections.values().cloned().collect())
}

pub async fn query_connection(
    pool: &PgPool,
    query_height: &QueryHeight,
    id: &ConnectionId,
) -> Result<Option<IdentifiedConnectionEnd>, Error> {
    let result = query_ibc_data(pool, query_height).await?;
    Ok(result.json_data.connections.get(id).cloned())
}

pub async fn query_channels(
    pool: &PgPool,
    query_height: &QueryHeight,
) -> Result<Vec<IdentifiedChannelEnd>, Error> {
    let result = query_ibc_data(pool, query_height).await?;
    Ok(result.json_data.channels.values().cloned().collect())
}

pub async fn query_channel(
    pool: &PgPool,
    query_height: &QueryHeight,
    id: &ChannelId,
) -> Result<Option<IdentifiedChannelEnd>, Error> {
    let result = query_ibc_data(pool, query_height).await?;
    Ok(result.json_data.channels.get(id).cloned())
}

pub async fn query_sent_packets(
    pool: &PgPool,
    query_height: &QueryHeight,
) -> Result<(Height, Vec<Packet>), Error> {
    let result = query_ibc_data(pool, query_height).await?;

    Ok((
        result.json_data.app_status.height,
        result
            .json_data
            .pending_sent_packets
            .values()
            .cloned()
            .collect(),
    ))
}

pub async fn query_sent_packet(
    pool: &PgPool,
    query_height: &QueryHeight,
    id: &PacketId,
) -> Result<Option<Packet>, Error> {
    let result = query_ibc_data(pool, query_height).await?;
    let p = result.json_data.pending_sent_packets.get(id).cloned();
    Ok(p)
}
