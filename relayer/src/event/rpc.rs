use alloc::collections::BTreeMap as HashMap;
use core::convert::TryFrom;

use tendermint_rpc::{event::Event as RpcEvent, event::EventData as RpcEventData};

use ibc::core::ics02_client::{events as ClientEvents, height::Height};
use ibc::core::ics03_connection::events as ConnectionEvents;
use ibc::core::ics04_channel::{events as ChannelEvents, msgs as chan_msgs};
use ibc::core::ics24_host::identifier::ChainId;
use ibc::events::{Error as EventError, IbcEvent, RawObject};

use crate::event::monitor::queries;

pub fn get_all_events(
    chain_id: &ChainId,
    result: RpcEvent,
) -> Result<Vec<(Height, IbcEvent)>, String> {
    let mut vals: Vec<(Height, IbcEvent)> = vec![];
    let RpcEvent { data, events, .. } = result;
    let events = events.ok_or("missing events")?;

    match data {
        RpcEventData::NewBlock { block, .. } => {
            let height = Height::new(
                ChainId::chain_version(chain_id.to_string().as_str()),
                u64::from(block.as_ref().ok_or("tx.height")?.header.height),
            );

            vals.push((height, ClientEvents::NewBlock::new(height).into()));

            let mut chan_events = vec![];
            let actions_and_indices = extract_helper(&events)?;
            for action in actions_and_indices {
                if let Ok(event) = build_channel_event(RawObject::new(
                    height,
                    action.0,
                    action.1 as usize,
                    &events,
                )) {
                    chan_events.push((height, event));
                }
            }
            chan_events.sort_by(|a, b| {
                let a = ChannelEventType::from(&a.1);
                let b = ChannelEventType::from(&b.1);
                a.cmp(&b)
            });

            vals.append(&mut chan_events);
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
                        let _span = tracing::trace_span!("ibc_channel event").entered();
                        tracing::trace!("extracted {:?}", chan_event);
                        if matches!(chan_event, IbcEvent::SendPacket(_)) {
                            // Should be the same as the hash of tx_result.tx?
                            if let Some(hash) =
                                events.get("tx.hash").and_then(|values| values.get(0))
                            {
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

pub fn build_channel_event(mut object: RawObject<'_>) -> Result<IbcEvent, EventError> {
    match object.action.as_str() {
        // Channel events
        "channel_open_init" | chan_msgs::chan_open_init::TYPE_URL => {
            Ok(IbcEvent::from(ChannelEvents::OpenInit::try_from(object)?))
        }
        "channel_open_try" | chan_msgs::chan_open_try::TYPE_URL => {
            Ok(IbcEvent::from(ChannelEvents::OpenTry::try_from(object)?))
        }
        "channel_open_ack" | chan_msgs::chan_open_ack::TYPE_URL => {
            Ok(IbcEvent::from(ChannelEvents::OpenAck::try_from(object)?))
        }
        "channel_open_confirm" | chan_msgs::chan_open_confirm::TYPE_URL => Ok(IbcEvent::from(
            ChannelEvents::OpenConfirm::try_from(object)?,
        )),
        "channel_close_init" | chan_msgs::chan_close_init::TYPE_URL => {
            Ok(IbcEvent::from(ChannelEvents::CloseInit::try_from(object)?))
        }
        "channel_close_confirm" | chan_msgs::chan_close_confirm::TYPE_URL => Ok(IbcEvent::from(
            ChannelEvents::CloseConfirm::try_from(object)?,
        )),

        // Packet events
        // Note: There is no message.action "send_packet", the only one we can hook into is the
        // module's action:
        // - "transfer" for ICS20
        // - "MsgSend" and "MsgRegister" for ICS27
        // However the attributes are all prefixed with "send_packet" therefore the overwrite here
        // TODO: This need to be sorted out
        "transfer"
        | ibc::applications::ics20_fungible_token_transfer::msgs::transfer::TYPE_URL
        | ibc::applications::ics27_interchain_accounts::ICS27_BANK_SEND_TYPE_URL
        | ibc::applications::ics27_interchain_accounts::ICS27_SEND_TYPE_URL
        | ibc::applications::ics27_interchain_accounts::ICS27_REGISTER_TYPE_URL => {
            object.action = "send_packet".to_string();
            Ok(IbcEvent::from(ChannelEvents::SendPacket::try_from(object)?))
        }
        // Same here
        // TODO: sort this out
        "recv_packet" | chan_msgs::recv_packet::TYPE_URL => {
            object.action = "write_acknowledgement".to_string();
            Ok(IbcEvent::from(
                ChannelEvents::WriteAcknowledgement::try_from(object)?,
            ))
        }
        "write_acknowledgement" => Ok(IbcEvent::from(
            ChannelEvents::WriteAcknowledgement::try_from(object)?,
        )),
        "acknowledge_packet" | chan_msgs::acknowledgement::TYPE_URL => {
            object.action = "acknowledge_packet".to_string();
            Ok(IbcEvent::from(ChannelEvents::AcknowledgePacket::try_from(
                object,
            )?))
        }
        "timeout_packet" | chan_msgs::timeout::TYPE_URL => {
            object.action = "timeout_packet".to_string();
            Ok(IbcEvent::from(ChannelEvents::TimeoutPacket::try_from(
                object,
            )?))
        }
        "timeout_on_close_packet" | chan_msgs::timeout_on_close::TYPE_URL => {
            object.action = "timeout_packet".to_string();
            Ok(IbcEvent::from(
                ChannelEvents::TimeoutOnClosePacket::try_from(object)?,
            ))
        }

        event_type => Err(EventError::incorrect_event_type(event_type.to_string())),
    }
}

/// Takes events in the form
///
/// ```json
/// {
///   "events": {
///     "connection_open_init.client_id": [
///       "testclient",
///       "testclientsec"
///     ],
///     "connection_open_init.connection_id": [
///       "ancaconnonetest",
///       "ancaconnonetestsec"
///     ],
///     "connection_open_init.counterparty_client_id": [
///       "testclientsec",
///       "testclientsecsec"
///     ],
///     "create_client.client_id": [
///       "testclientthird"
///     ],
///     "create_client.client_type": [
///       "tendermint"
///     ],
///     "message.action": [
///       "connection_open_init",
///       "create_client",
///       "connection_open_init"
///     ],
///     "message.module": [
///       "ibc_connection",
///       "ibc_client",
///       "ibc_connection"
///     ],
///     "message.sender": [
///       "cosmos187xxg4yfkypl05cqylucezpjvycj24nurvm8p9",
///       "cosmos187xxg4yfkypl05cqylucezpjvycj24nurvm8p9",
///       "cosmos187xxg4yfkypl05cqylucezpjvycj24nurvm8p9",
///       "cosmos187xxg4yfkypl05cqylucezpjvycj24nurvm8p9"
///     ],
///     "tm.event": [
///       "Tx"
///     ],
///     "transfer.amount": [
///       "5000stake"
///     ],
///     "transfer.recipient": [
///       "cosmos17xpfvakm2amg962yls6f84z3kell8c5lserqta"
///     ],
///     "tx.hash": [
///       "A9E18AE3909F22232F8DBDB1C48F2FECB260A308A2D157E8832E901D45950605"
///     ],
///     "tx.height": [
///       "35"
///     ]
///   }
/// }
/// ```
///
/// and returns:
///
/// ```rust
/// vec![
///     ("connection_open_init", 0),
///     ("create_client", 0),
///     ("connection_open_init", 1),
/// ];
/// ```
///
/// where the number in each entry is the index in the matching events that should be used to build the event.
///
/// e.g. for the last "connection_open_init" in the result
///
/// ```text
/// "connection_open_init.client_id"              -> "testclientsec"
/// "connection_open_init.connection_id"          -> "ancaconnonetestsec",
/// "connection_open_init.counterparty_client_id" -> "testclientsec", "testclientsecsec",
/// ```
fn extract_helper(events: &HashMap<String, Vec<String>>) -> Result<Vec<(String, u32)>, String> {
    let actions = events.get("message.action").ok_or("Incorrect Event Type")?;

    let mut val_indices = HashMap::new();
    let mut result = Vec::with_capacity(actions.len());

    for action in actions {
        let idx = val_indices.entry(action.clone()).or_insert_with(|| 0);
        result.push((action.clone(), *idx));

        *val_indices.get_mut(action.as_str()).unwrap() += 1;
    }

    Ok(result)
}

// A type that is used to derive the ordering for channel events.
// Events are ordered in the following order -> `Open > Packet > Close`.
#[derive(Eq, PartialEq, PartialOrd, Ord)]
enum ChannelEventType {
    Open,
    Packet,
    Close,
}

impl From<&IbcEvent> for ChannelEventType {
    fn from(ev: &IbcEvent) -> Self {
        match ev {
            IbcEvent::OpenInitChannel(_)
            | IbcEvent::OpenTryChannel(_)
            | IbcEvent::OpenAckChannel(_)
            | IbcEvent::OpenConfirmChannel(_) => Self::Open,
            IbcEvent::CloseInitChannel(_) | IbcEvent::CloseConfirmChannel(_) => Self::Close,
            IbcEvent::SendPacket(_)
            | IbcEvent::ReceivePacket(_)
            | IbcEvent::WriteAcknowledgement(_)
            | IbcEvent::AcknowledgePacket(_)
            | IbcEvent::TimeoutPacket(_)
            | IbcEvent::TimeoutOnClosePacket(_) => Self::Packet,
            _ => unreachable!(),
        }
    }
}
