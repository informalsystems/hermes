use alloc::collections::BTreeMap as HashMap;

use tendermint_rpc::{event::Event as RpcEvent, event::EventData as RpcEventData};

use ibc::core::ics02_client::{events as ClientEvents, height::Height};
use ibc::core::ics03_connection::events as ConnectionEvents;
use ibc::core::ics04_channel::events as ChannelEvents;
use ibc::core::ics24_host::identifier::ChainId;
use ibc::events::{IbcEvent, RawObject};

use crate::event::monitor::queries;

pub fn get_all_events(
    chain_id: &ChainId,
    result: RpcEvent,
) -> Result<Vec<(Height, IbcEvent)>, String> {
    let mut vals: Vec<(Height, IbcEvent)> = vec![];

    match &result.data {
        RpcEventData::NewBlock { block, .. } => {
            let height = Height::new(
                ChainId::chain_version(chain_id.to_string().as_str()),
                u64::from(block.as_ref().ok_or("tx.height")?.header.height),
            );

            vals.push((height, ClientEvents::NewBlock::new(height).into()));

            if let Some(events) = &result.events {
                let ibc_events =
                    send_packet_from_block_events(height, events.clone().into_iter().collect());
                if !ibc_events.is_empty() {
                    vals.extend(ibc_events);
                }
            }
        }
        RpcEventData::Tx { tx_result } => {
            let height = Height::new(
                ChainId::chain_version(chain_id.to_string().as_str()),
                tx_result.height as u64,
            );

            for abci_event in &tx_result.result.events {
                let query = &result.query;
                if *query == queries::ibc_client().to_string() {
                    if let Some(mut client_event) = ClientEvents::try_from_tx(abci_event) {
                        client_event.set_height(height);
                        tracing::trace!("extracted ibc_client event {:?}", client_event);
                        vals.push((height, client_event));
                    }
                }
                if *query == queries::ibc_connection().to_string() {
                    if let Some(mut conn_event) = ConnectionEvents::try_from_tx(abci_event) {
                        conn_event.set_height(height);
                        tracing::trace!("extracted ibc_connection event {:?}", conn_event);
                        vals.push((height, conn_event));
                    }
                }
                if *query == queries::ibc_channel().to_string() {
                    if let Some(mut chan_event) = ChannelEvents::try_from_tx(abci_event) {
                        chan_event.set_height(height);
                        tracing::trace!("extracted ibc_channel event {:?}", chan_event);
                        vals.push((height, chan_event));
                    }
                }
            }
        }
        _ => {}
    }

    Ok(vals)
}

fn send_packet_from_block_events(
    height: Height,
    events: HashMap<String, Vec<String>>,
) -> Vec<(Height, IbcEvent)> {
    let mut vals: Vec<(Height, IbcEvent)> = vec![];
    if let Some(packets) = events.get("send_packet.packet_data") {
        for i in 0..packets.len() {
            let raw_obj = RawObject::new(height, "send_packet".to_string(), i, events.clone());

            if let Ok(pkg) = ChannelEvents::SendPacket::try_from(raw_obj) {
                vals.push((height, IbcEvent::from(pkg)))
            }
        }
    }
    vals
}
