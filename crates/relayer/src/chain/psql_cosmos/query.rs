// use tendermint::abci::{self, Event};
// use tendermint_rpc::endpoint::tx::Response as ResultTx;

use ibc_relayer_types::core::ics04_channel::events::SendPacket;
// use ibc_relayer_types::core::ics02_client::height::Height;
// use ibc_relayer_types::core::ics04_channel::packet::Packet;
use ibc_relayer_types::events::{IbcEvent, WithBlockDataType};
// use ibc_relayer_types::Height as ICSHeight;

// use crate::chain::cosmos::types::events::from_tx_response_event;

use crate::chain::requests::*;

use crate::error::Error;
use crate::event::IbcEventWithHeight;
use crate::snapshot::{PacketId, SnapshotStore};

#[tracing::instrument(skip(snapshot_store))]
pub async fn query_send_packets_from_ibc_snapshot(
    snapshot_store: &dyn SnapshotStore,
    request: &QueryPacketEventDataRequest,
) -> Result<Vec<IbcEventWithHeight>, Error> {
    crate::time!("query_send_packets_from_ibc_snapshot");

    assert_eq!(request.event_id, WithBlockDataType::SendPacket);

    let (height, all_packets) = snapshot_store
        .query_sent_packets(request.height.get())
        .await?;

    let events = all_packets
        .into_iter()
        .filter_map(|event| {
            if event.src_port_id() == &request.source_port_id
                && event.src_channel_id() == &request.source_channel_id
                && request.sequences.contains(&event.sequence())
            {
                Some(IbcEventWithHeight::new(IbcEvent::SendPacket(event), height))
            } else {
                None
            }
        })
        .collect();

    Ok(events)
}

#[tracing::instrument(skip(snapshot_store))]
pub async fn update_send_packets_in_ibc_snapshot(
    snapshot_store: &mut dyn SnapshotStore,
    request: &QueryPacketEventDataRequest,
    events: &[SendPacket],
) -> Result<(), Error> {
    crate::time!("query_send_packets_from_ibc_snapshot");

    let snapshot = snapshot_store.fetch_snapshot(request.height.get()).await?;
    let mut snapshot = snapshot.into_owned();

    for send_packet in events {
        let packet_id = PacketId {
            channel_id: request.source_channel_id.clone(),
            port_id: request.source_port_id.clone(),
            sequence: send_packet.packet.sequence,
        };

        snapshot
            .data
            .pending_sent_packets
            .entry(packet_id)
            .or_insert_with(|| send_packet.clone());
    }

    snapshot_store.update_snapshot(&snapshot).await?;

    Ok(())
}

// /// This function queries transactions for events matching certain criteria.
// /// 1. Client Update request - returns a vector with at most one update client event
// /// 2. Packet event request - returns at most one packet event for each sequence specified
// ///    in the request.
// fn filter_matching_event(
//     event: Event,
//     height: Height,
//     request: &QueryPacketEventDataRequest,
// ) -> Option<IbcEventWithHeight> {
//     fn matches_packet(request: &QueryPacketEventDataRequest, packet: &Packet) -> bool {
//         packet.source_port == request.source_port_id
//             && packet.source_channel == request.source_channel_id
//             && packet.destination_port == request.destination_port_id
//             && packet.destination_channel == request.destination_channel_id
//             && request.sequences.contains(&packet.sequence)
//     }

//     if event.kind != request.event_id.as_str() {
//         return None;
//     }

//     let ibc_event = from_tx_response_event(height, &event)?;

//     match ibc_event.event {
//         IbcEvent::SendPacket(ref send_ev) if matches_packet(request, &send_ev.packet) => {
//             Some(ibc_event)
//         }
//         IbcEvent::WriteAcknowledgement(ref ack_ev) if matches_packet(request, &ack_ev.packet) => {
//             Some(ibc_event)
//         }
//         _ => None,
//     }
// }

// fn all_ibc_events_from_tx_search_response(
//     height: ICSHeight,
//     result: abci::response::DeliverTx,
// ) -> Vec<IbcEventWithHeight> {
//     let mut events = vec![];
//     for event in result.events {
//         if let Some(ibc_ev) = from_tx_response_event(height, &event) {
//             events.push(ibc_ev);
//         }
//     }
//     events
// }

// // Extracts from the Tx the update client event for the requested client and height.
// // Note: in the Tx, there may have been multiple events, some of them may be
// // for update of other clients that are not relevant to the request.
// // For example, if we're querying for a transaction that includes the update for client X at
// // consensus height H, it is possible that the transaction also includes an update client
// // for client Y at consensus height H'. This is the reason the code iterates all event fields in the
// // returned Tx to retrieve the relevant ones.
// // Returns `None` if no matching event was found.
// fn update_client_events_from_tx_search_response(
//     chain_id: &ChainId,
//     request: &QueryClientEventRequest,
//     response: ResultTx,
// ) -> Option<IbcEventWithHeight> {
//     let height = ICSHeight::new(chain_id.version(), u64::from(response.height)).unwrap();
//     if let QueryHeight::Specific(query_height) = request.query_height {
//         if height > query_height {
//             return None;
//         }
//     }

//     response
//         .tx_result
//         .events
//         .into_iter()
//         .filter(|event| event.kind == request.event_id.as_str())
//         .flat_map(|event| from_tx_response_event(height, &event))
//         .flat_map(|event| match event.event {
//             IbcEvent::UpdateClient(update) => Some(update),
//             _ => None,
//         })
//         .find(|update| {
//             update.common.client_id == request.client_id
//                 && update.common.consensus_height == request.consensus_height
//         })
//         .map(|update| IbcEventWithHeight::new(IbcEvent::UpdateClient(update), height))
// }

// // Extract the packet events from the query_txs RPC responses.
// fn packet_events_from_tx_search_response(
//     chain_id: &ChainId,
//     request: &QueryPacketEventDataRequest,
//     responses: Vec<ResultTx>,
// ) -> Vec<IbcEventWithHeight> {
//     let mut events = vec![];

//     for response in responses {
//         let height = ICSHeight::new(chain_id.version(), u64::from(response.height)).unwrap();

//         if let QueryHeight::Specific(specific_query_height) = request.height.get() {
//             if height > specific_query_height {
//                 continue;
//             }
//         };

//         let mut new_events = response
//             .tx_result
//             .events
//             .into_iter()
//             .filter_map(|ev| filter_matching_event(ev, height, request))
//             .collect::<Vec<_>>();

//         events.append(&mut new_events)
//     }

//     events
// }

// #[tracing::instrument]
// pub async fn query_txs_from_ibc_snapshots(
//     chain_id: &ChainId,
//     search: &QueryTxRequest,
// ) -> Result<Vec<IbcEventWithHeight>, Error> {
//     // TODO(romac): implement this to actually query for client updates or Tx hash from snapshots
//     todo!()
// }

// fn all_ibc_events_from_tx_result_batch(
//     chain_id: &ChainId,
//     responses: Vec<ResultTx>,
// ) -> Vec<Vec<IbcEventWithHeight>> {
//     let mut events = vec![];

//     for response in responses {
//         let height = ICSHeight::new(chain_id.version(), u64::from(response.height)).unwrap();

//         let new_events = if response.tx_result.code.is_err() {
//             vec![IbcEventWithHeight::new(
//                 IbcEvent::ChainError(format!(
//                     "deliver_tx on chain {} for Tx hash {} reports error: code={:?}, log={:?}",
//                     chain_id, response.hash, response.tx_result.code, response.tx_result.log
//                 )),
//                 height,
//             )]
//         } else {
//             response
//                 .tx_result
//                 .events
//                 .into_iter()
//                 .filter_map(|ev| from_tx_response_event(height, &ev))
//                 .collect::<Vec<_>>()
//         };
//         events.push(new_events)
//     }
//     events
// }
