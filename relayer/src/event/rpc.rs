use tendermint_rpc::{abci, event::Event as RpcEvent, event::EventData as RpcEventData};

use ibc::core::ics02_client::events::NewBlock;
use ibc::core::ics02_client::height::Height;
use ibc::core::ics24_host::identifier::ChainId;
use ibc::events::IbcEvent;

use super::ics02_client as client_events;
use super::ics03_connection as connection_events;
use super::ics04_channel as channel_events;
use crate::event::monitor::queries;

/// Extract IBC events from Tendermint RPC events
///
/// Events originate from the following ABCI methods ->
/// 1. `DeliverTx` - these events are generated during the execution of transaction messages.
/// 2. `BeginBlock`
/// 3. `EndBlock`
///
/// Events originating from `DeliverTx` are currently extracted via the `RpcEvent::data` field as
/// the `EventData::Tx` variant.
/// Here's an example of what these events look like (i.e. `TxInfo::TxResult::events`) -
/// ```ron
/// [
///     Event {
///         type_str: "channel_open_init",
///         attributes: [
///             Tag {
///                 key: Key(
///                     "port_id",
///                 ),
///                 value: Value(
///                     "transfer",
///                 ),
///             },
///             Tag {
///                 key: Key(
///                     "channel_id",
///                 ),
///                 value: Value(
///                     "channel-1",
///                 ),
///             },
///             Tag {
///                 key: Key(
///                     "counterparty_port_id",
///                 ),
///                 value: Value(
///                     "transfer",
///                 ),
///             },
///             Tag {
///                 key: Key(
///                     "counterparty_channel_id",
///                 ),
///                 value: Value(
///                     "",
///                 ),
///             },
///             Tag {
///                 key: Key(
///                     "connection_id",
///                 ),
///                 value: Value(
///                     "connection-1",
///                 ),
///             },
///         ],
///     },
///     // ...
/// ]
/// ```
///
/// Events originating from `BeginBlock` and `EndBlock` methods are extracted via the
/// `RpcEvent::events` field. As of tendermint-rs 0.24, these also look as shown
/// in the example above.
pub fn get_all_events(
    chain_id: &ChainId,
    result: RpcEvent,
) -> Result<Vec<(Height, IbcEvent)>, String> {
    let mut vals: Vec<(Height, IbcEvent)> = vec![];
    let RpcEvent {
        data,
        events,
        query,
    } = result;
    let events = events.ok_or("missing events")?;

    match data {
        RpcEventData::NewBlock { block, .. } if query == queries::new_block().to_string() => {
            let height = Height::new(
                ChainId::chain_version(chain_id.to_string().as_str()),
                u64::from(block.as_ref().ok_or("tx.height")?.header.height),
            );

            vals.push((height, NewBlock::new(height).into()));
            vals.append(&mut extract_block_events(height, &events));
        }
        RpcEventData::Tx { tx_result } => {
            let height = Height::new(
                ChainId::chain_version(chain_id.to_string().as_str()),
                tx_result.height as u64,
            );

            for abci_event in &tx_result.result.events {
                if query == queries::ibc_client().to_string() {
                    if let Some(mut client_event) = client_events::try_from_tx(abci_event) {
                        client_event.set_height(height);
                        tracing::trace!("extracted ibc_client event {}", client_event);
                        vals.push((height, client_event));
                    }
                }
                if query == queries::ibc_connection().to_string() {
                    if let Some(mut conn_event) = connection_events::try_from_tx(abci_event) {
                        conn_event.set_height(height);
                        tracing::trace!("extracted ibc_connection event {}", conn_event);
                        vals.push((height, conn_event));
                    }
                }
                if query == queries::ibc_channel().to_string() {
                    if let Some(mut chan_event) = channel_events::try_from_tx(abci_event) {
                        chan_event.set_height(height);
                        let _span = tracing::trace_span!("ibc_channel event").entered();
                        tracing::trace!("extracted {}", chan_event);
                        if matches!(chan_event, IbcEvent::SendPacket(_)) {
                            // Should be the same as the hash of tx_result.tx?
                            if let Some(hash) = extract_abci_event_tag(&events, "tx", "hash") {
                                tracing::trace!(event = "SendPacket", "tx hash: {}", hash);
                            }
                        }
                        vals.push((height, chan_event));
                    }
                }
            }
        }
        _ => {}
    }

    Ok(vals)
}

fn extract_block_events(height: Height, block_events: &[abci::Event]) -> Vec<(Height, IbcEvent)> {
    let mut events: Vec<(Height, IbcEvent)> = vec![];
    for abci_ev in block_events {
        if let Some(ev) = channel_events::try_from_tx(abci_ev) {
            events.push((height, ev));
        }
    }
    events
}

fn extract_abci_event_tag<'a>(
    events: &'a [abci::Event],
    type_str: &str,
    key: &str,
) -> Option<&'a str> {
    for event in events {
        if event.type_str == type_str {
            for tag in &event.attributes {
                if tag.key.as_ref() == key {
                    return Some(tag.value.as_ref());
                }
            }
        }
    }
    None
}
