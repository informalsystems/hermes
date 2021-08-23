use std::{collections::HashMap, convert::TryFrom};

use tendermint_rpc::event::{Event as RpcEvent, EventData as RpcEventData};

use ibc::ics02_client::events::NewBlock;
use ibc::ics02_client::height::Height;
use ibc::ics24_host::identifier::ChainId;
use ibc::{
    events::{Error as EventError, IbcEvent, RawObject},
    ics02_client::events as ClientEvents,
    ics03_connection::events as ConnectionEvents,
    ics04_channel::events as ChannelEvents,
};

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
        }

        RpcEventData::Tx { .. } => {
            let events = &result.events.ok_or("missing events")?;
            let height_raw = events.get("tx.height").ok_or("tx.height")?[0]
                .parse::<u64>()
                .map_err(|e| e.to_string())?;
            let height = Height::new(
                ChainId::chain_version(chain_id.to_string().as_str()),
                height_raw,
            );

            let actions_and_indices = extract_helper(events)?;
            for action in actions_and_indices {
                if let Ok(event) = build_event(RawObject::new(
                    height,
                    action.0,
                    action.1 as usize,
                    events.clone(),
                )) {
                    vals.push((height, event));
                }
            }
        }
        _ => {}
    }

    Ok(vals)
}

pub fn build_event(mut object: RawObject) -> Result<IbcEvent, EventError> {
    match object.action.as_str() {
        // Client events
        "create_client" | ibc::ics02_client::msgs::create_client::TYPE_URL => Ok(IbcEvent::from(
            ClientEvents::CreateClient::try_from(object)?,
        )),
        "update_client" | ibc::ics02_client::msgs::update_client::TYPE_URL => Ok(IbcEvent::from(
            ClientEvents::UpdateClient::try_from(object)?,
        )),
        "submit_misbehaviour" | ibc::ics02_client::msgs::misbehavior::TYPE_URL => Ok(
            IbcEvent::from(ClientEvents::ClientMisbehaviour::try_from(object)?),
        ),

        // Connection events
        "connection_open_init" | ibc::ics03_connection::msgs::conn_open_init::TYPE_URL => Ok(
            IbcEvent::from(ConnectionEvents::OpenInit::try_from(object)?),
        ),
        "connection_open_try" | ibc::ics03_connection::msgs::conn_open_try::TYPE_URL => {
            Ok(IbcEvent::from(ConnectionEvents::OpenTry::try_from(object)?))
        }
        "connection_open_ack" | ibc::ics03_connection::msgs::conn_open_ack::TYPE_URL => {
            Ok(IbcEvent::from(ConnectionEvents::OpenAck::try_from(object)?))
        }
        "connection_open_confirm" | ibc::ics03_connection::msgs::conn_open_confirm::TYPE_URL => Ok(
            IbcEvent::from(ConnectionEvents::OpenConfirm::try_from(object)?),
        ),

        // Channel events
        "channel_open_init" | ibc::ics04_channel::msgs::chan_open_init::TYPE_URL => {
            Ok(IbcEvent::from(ChannelEvents::OpenInit::try_from(object)?))
        }
        "channel_open_try" | ibc::ics04_channel::msgs::chan_open_try::TYPE_URL => {
            Ok(IbcEvent::from(ChannelEvents::OpenTry::try_from(object)?))
        }
        "channel_open_ack" | ibc::ics04_channel::msgs::chan_open_ack::TYPE_URL => {
            Ok(IbcEvent::from(ChannelEvents::OpenAck::try_from(object)?))
        }
        "channel_open_confirm" | ibc::ics04_channel::msgs::chan_open_confirm::TYPE_URL => Ok(
            IbcEvent::from(ChannelEvents::OpenConfirm::try_from(object)?),
        ),
        "channel_close_init" | ibc::ics04_channel::msgs::chan_close_init::TYPE_URL => {
            Ok(IbcEvent::from(ChannelEvents::CloseInit::try_from(object)?))
        }
        "channel_close_confirm" | ibc::ics04_channel::msgs::chan_close_confirm::TYPE_URL => Ok(
            IbcEvent::from(ChannelEvents::CloseConfirm::try_from(object)?),
        ),

        // Packet events
        // Note: There is no message.action "send_packet", the only one we can hook into is the
        // module's action:
        // - "transfer" for ICS20
        // - "MsgSend" and "MsgRegister" for ICS27
        // However the attributes are all prefixed with "send_packet" therefore the overwrite here
        // TODO: This need to be sorted out
        "transfer"
        | ibc::application::ics20_fungible_token_transfer::msgs::transfer::TYPE_URL
        | ibc::application::ICS27_BANK_SEND_TYPE_URL
        | ibc::application::ICS27_SEND_TYPE_URL
        | ibc::application::ICS27_REGISTER_TYPE_URL => {
            object.action = "send_packet".to_string();
            Ok(IbcEvent::from(ChannelEvents::SendPacket::try_from(object)?))
        }
        // Same here
        // TODO: sort this out
        "recv_packet" | ibc::ics04_channel::msgs::recv_packet::TYPE_URL => {
            object.action = "write_acknowledgement".to_string();
            Ok(IbcEvent::from(
                ChannelEvents::WriteAcknowledgement::try_from(object)?,
            ))
        }
        "write_acknowledgement" => Ok(IbcEvent::from(
            ChannelEvents::WriteAcknowledgement::try_from(object)?,
        )),
        "acknowledge_packet" | ibc::ics04_channel::msgs::acknowledgement::TYPE_URL => {
            object.action = "acknowledge_packet".to_string();
            Ok(IbcEvent::from(ChannelEvents::AcknowledgePacket::try_from(
                object,
            )?))
        }
        "timeout_packet" | ibc::ics04_channel::msgs::timeout::TYPE_URL => {
            object.action = "timeout_packet".to_string();
            Ok(IbcEvent::from(ChannelEvents::TimeoutPacket::try_from(
                object,
            )?))
        }
        "timeout_on_close_packet" | ibc::ics04_channel::msgs::timeout_on_close::TYPE_URL => {
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
