use tendermint_rpc::{abci, event::Event as RpcEvent, event::EventData as RpcEventData};

use ibc::core::ics02_client::{events as client_events, height::Height};
use ibc::core::ics03_connection::events as connection_events;
use ibc::core::ics04_channel::events as channel_events;
use ibc::core::ics24_host::identifier::ChainId;
use ibc::events::IbcEvent;

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
/// `RpcEvent::events` field. Here's an example of what these events look like ->
/// ```json
/// {
///     "channel_open_init.channel_id": [
///         "channel-0",
///     ],
///     "channel_open_init.connection_id": [
///         "connection-0",
///     ],
///     "channel_open_init.counterparty_channel_id": [
///         "channel-0",
///     ],
///     "channel_open_init.counterparty_port_id": [
///         "transfer",
///     ],
///     "channel_open_init.port_id": [
///         "transfer",
///     ],
///     // ...
/// }
/// ```
///
/// Note: Historically, all events were extracted from the `RpcEvent::events` field. This was
/// possible because these events had a `message.action` field that allowed us to infer the order in
/// which these events were triggered ->
/// ```json
/// "message.action": [
///     "update_client",
///     "channel_open_ack",
/// ],
/// "message.module": [
///     "ibc_client",
///     "ibc_channel",
/// ],
/// ```
/// {Begin,End}Block events however do not have any such `message.action` associated with them, so
/// this doesn't work. For this reason, we extract block events in the following order ->
/// OpenInit -> OpenTry -> OpenAck -> OpenConfirm -> SendPacket -> CloseInit -> CloseConfirm.
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

            vals.push((height, client_events::NewBlock::new(height).into()));
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
                            // We are interested in the tag "hash" of an event with type "tx",
                            // but this is trace level, so print the whole list of events.
                            // Should be the same as the hash of tx_result.tx?
                            // TODO: use a helper function to filter to just the interesting
                            // information, or remove the whole log event if it's no longer needed.
                            tracing::trace!(event = "SendPacket", "ABCI events: {:?}", events);
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
