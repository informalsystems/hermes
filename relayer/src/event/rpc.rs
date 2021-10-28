use alloc::collections::BTreeMap as HashMap;

use tendermint_rpc::event::{Event as RpcEvent, EventData as RpcEventData};

use ibc::core::ics02_client::events::NewBlock;
use ibc::core::ics02_client::height::Height;
use ibc::core::ics04_channel::events as ChannelEvents;
use ibc::core::ics24_host::identifier::ChainId;
use ibc::events::{from_tx_response_event, IbcEvent, RawObject};

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

            vals.push((height, NewBlock::new(height).into()));

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
                if let Some(ibc_event) = from_tx_response_event(height, abci_event) {
                    tracing::trace!("Extracted ibc_event {:?}", ibc_event);
                    vals.push((height, ibc_event));
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
