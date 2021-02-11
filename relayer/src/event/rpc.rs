use std::{
    collections::HashMap,
    convert::{TryFrom, TryInto},
};

use anomaly::BoxError;
use tracing::warn;

use tendermint::block::Height;
use tendermint_rpc::event::{Event as RpcEvent, EventData as RpcEventData};

use ibc::{
    events::{IBCEvent, RawObject},
    ics02_client::events as ClientEvents,
    ics03_connection::events as ConnectionEvents,
    ics04_channel::events as ChannelEvents,
};

pub fn get_all_events(result: RpcEvent) -> Result<Vec<(Height, IBCEvent)>, String> {
    let mut vals: Vec<(Height, IBCEvent)> = vec![];

    match &result.data {
        RpcEventData::NewBlock { block, .. } => {
            let block = block.as_ref().ok_or("missing block")?;
            vals.push((
                block.header.height,
                ClientEvents::NewBlock::new(block.header.height).into(),
            ));
        }

        RpcEventData::Tx { .. } => {
            let events = &result.events.ok_or("missing events")?;
            let height_raw = events.get("tx.height").ok_or("tx.height")?[0]
                .parse::<u64>()
                .map_err(|e| e.to_string())?;

            let height: Height = height_raw
                .try_into()
                .map_err(|_| "height parsing overflow")?;

            let actions_and_indices = extract_helper(&events)?;
            for action in actions_and_indices {
                match build_event(RawObject::new(
                    height,
                    action.0,
                    action.1 as usize,
                    events.clone(),
                )) {
                    Ok(event) => vals.push((height, event)),
                    Err(e) => warn!("error while building event {}", e.to_string()),
                }
            }
        }
        _ => {}
    }

    Ok(vals)
}

pub fn build_event(mut object: RawObject) -> Result<IBCEvent, BoxError> {
    match object.action.as_str() {
        // Client events
        "create_client" => Ok(IBCEvent::from(ClientEvents::CreateClient::try_from(
            object,
        )?)),
        "update_client" => Ok(IBCEvent::from(ClientEvents::UpdateClient::try_from(
            object,
        )?)),

        // Connection events
        "connection_open_init" => Ok(IBCEvent::from(ConnectionEvents::OpenInit::try_from(
            object,
        )?)),
        "connection_open_try" => Ok(IBCEvent::from(ConnectionEvents::OpenTry::try_from(object)?)),
        "connection_open_ack" => Ok(IBCEvent::from(ConnectionEvents::OpenAck::try_from(object)?)),
        "connection_open_confirm" => Ok(IBCEvent::from(ConnectionEvents::OpenConfirm::try_from(
            object,
        )?)),

        // Channel events
        "channel_open_init" => Ok(IBCEvent::from(ChannelEvents::OpenInit::try_from(object)?)),
        "channel_open_try" => Ok(IBCEvent::from(ChannelEvents::OpenTry::try_from(object)?)),
        "channel_open_ack" => Ok(IBCEvent::from(ChannelEvents::OpenAck::try_from(object)?)),
        "channel_open_confirm" => Ok(IBCEvent::from(ChannelEvents::OpenConfirm::try_from(
            object,
        )?)),
        "channel_close_init" => Ok(IBCEvent::from(ChannelEvents::CloseInit::try_from(object)?)),
        "channel_close_confirm" => Ok(IBCEvent::from(ChannelEvents::CloseConfirm::try_from(
            object,
        )?)),

        // Packet events
        // Note: There is no message.action "send_packet", the only one we can hook into is the
        // module's action, "transfer" being the only one in IBC1.0. However the attributes
        // are all prefixed with "send_packet" therefore the overwrite here
        // TODO: This need to be sorted out
        "transfer" => {
            object.action = "send_packet".to_string();
            Ok(IBCEvent::from(ChannelEvents::SendPacket::try_from(object)?))
        }
        // Same here
        // TODO: sort this out
        "recv_packet" => {
            object.action = "write_acknowledgement".to_string();
            Ok(IBCEvent::from(
                ChannelEvents::WriteAcknowledgement::try_from(object)?,
            ))
        }
        "write_acknowledgement" => Ok(IBCEvent::from(
            ChannelEvents::WriteAcknowledgement::try_from(object)?,
        )),
        "acknowledge_packet" => Ok(IBCEvent::from(ChannelEvents::AcknowledgePacket::try_from(
            object,
        )?)),
        "timeout_packet" => Ok(IBCEvent::from(ChannelEvents::TimeoutPacket::try_from(
            object,
        )?)),

        _ => Err("Incorrect Event Type".into()),
    }
}

/// Takes events in the form
///
/// ```json
///  "events":{
///      "connection_open_init.client_id":["testclient","testclientsec"],
///      "connection_open_init.connection_id":["ancaconnonetest","ancaconnonetestsec"],
///      "connection_open_init.counterparty_client_id":["testclientsec","testclientsecsec"],
///      "create_client.client_id":["testclientthird"],
///      "create_client.client_type":["tendermint"],
///      "message.action":["connection_open_init","create_client","connection_open_init"],
///      "message.module":["ibc_connection","ibc_client",ibc_connection"],
///      "message.sender":["cosmos187xxg4yfkypl05cqylucezpjvycj24nurvm8p9","cosmos187xxg4yfkypl05cqylucezpjvycj24nurvm8p9","cosmos187xxg4yfkypl05cqylucezpjvycj24nurvm8p9","cosmos187xxg4yfkypl05cqylucezpjvycj24nurvm8p9"],"tm.event":["Tx"],"transfer.amount":["5000stake"],"transfer.recipient":["cosmos17xpfvakm2amg962yls6f84z3kell8c5lserqta"],"tx.hash":["A9E18AE3909F22232F8DBDB1C48F2FECB260A308A2D157E8832E901D45950605"],
///      "tx.height":["35"]
/// ```
///
/// and returns:
///
/// ```json
/// [{"connection_open_init", 0}, {"create_client", 0}, {"connection_open_init", 1}]
/// ```
///
/// where the number in each entry is the index in the matching events that should be used to build the event.
///
/// e.g. for the last "connection_open_init" in the result
///
/// ```
///      "connection_open_init.client_id" -> "testclientsec"
///      "connection_open_init.connection_id" -> "ancaconnonetestsec",
///      "connection_open_init.counterparty_client_id" -> "testclientsec","testclientsecsec",
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
