use crate::application::ics20_fungible_token_transfer::events as TransferEvents;
use crate::ics02_client::events as ClientEvents;
use crate::ics02_client::events::NewBlock;
use crate::ics03_connection::events as ConnectionEvents;
use crate::ics04_channel::events as ChannelEvents;
use crate::Height as ICSHeight;

use tendermint_rpc::event::{Event as RpcEvent, EventData as RpcEventData};

use anomaly::BoxError;
use serde_derive::{Deserialize, Serialize};
use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};
use tendermint::block::Height;

use tracing::warn;

/// Events types
#[derive(Debug, Clone, Deserialize, Serialize)]
pub enum IBCEventType {
    CreateClient,
    SendPacket,
    WriteAck,
}

impl IBCEventType {
    pub fn as_str(&self) -> &'static str {
        match *self {
            IBCEventType::CreateClient => "create_client",
            IBCEventType::SendPacket => "send_packet",
            IBCEventType::WriteAck => "write_acknowledgement",
        }
    }
}

/// Events created by the IBC component of a chain, destined for a relayer.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub enum IBCEvent {
    NewBlock(NewBlock),

    CreateClient(ClientEvents::CreateClient),
    UpdateClient(ClientEvents::UpdateClient),
    ClientMisbehavior(ClientEvents::ClientMisbehavior),

    OpenInitConnection(ConnectionEvents::OpenInit),
    OpenTryConnection(ConnectionEvents::OpenTry),
    OpenAckConnection(ConnectionEvents::OpenAck),
    OpenConfirmConnection(ConnectionEvents::OpenConfirm),

    OpenInitChannel(ChannelEvents::OpenInit),
    OpenTryChannel(ChannelEvents::OpenTry),
    OpenAckChannel(ChannelEvents::OpenAck),
    OpenConfirmChannel(ChannelEvents::OpenConfirm),
    CloseInitChannel(ChannelEvents::CloseInit),
    CloseConfirmChannel(ChannelEvents::CloseConfirm),

    SendPacket(ChannelEvents::SendPacket),
    ReceivePacket(ChannelEvents::ReceivePacket),
    WriteAcknowledgement(ChannelEvents::WriteAcknowledgement),
    AcknowledgePacket(ChannelEvents::AcknowledgePacket),
    TimeoutPacket(ChannelEvents::TimeoutPacket),
    TimeoutOnClosePacket(ChannelEvents::TimeoutOnClosePacket),

    TimeoutTransfer(TransferEvents::Timeout),
    PacketTransfer(TransferEvents::Packet),
    ChannelClosedTransfer(TransferEvents::ChannelClosed),

    Empty(String),      // Special event, signifying empty response
    ChainError(String), // Special event, signifying an error on CheckTx or DeliverTx
}

// This is tendermint specific
pub fn from_tx_response_event(event: &tendermint::abci::Event) -> Option<IBCEvent> {
    // Return the first hit we find
    if let Some(client_res) = ClientEvents::try_from_tx(event) {
        Some(client_res)
    } else if let Some(conn_res) = ConnectionEvents::try_from_tx(event) {
        Some(conn_res)
    } else if let Some(chan_res) = ChannelEvents::try_from_tx(event) {
        Some(chan_res)
    } else {
        None
    }
}

impl IBCEvent {
    pub fn to_json(&self) -> String {
        serde_json::to_string(self).unwrap()
    }

    // TODO - change to ICSHeight
    pub fn height(&self) -> &Height {
        match self {
            IBCEvent::NewBlock(ev) => &ev.height,
            IBCEvent::UpdateClient(ev) => ev.height(),
            IBCEvent::SendPacket(ev) => &ev.height,
            IBCEvent::ReceivePacket(ev) => &ev.height,
            IBCEvent::WriteAcknowledgement(ev) => &ev.height,
            IBCEvent::AcknowledgePacket(ev) => &ev.height,
            IBCEvent::TimeoutPacket(ev) => &ev.height,
            IBCEvent::CloseInitChannel(ev) => ev.height(),

            _ => unimplemented!(),
        }
    }

    pub fn set_height(&mut self, height: &ICSHeight) {
        match self {
            IBCEvent::SendPacket(ev) => {
                ev.height = Height::try_from(height.revision_height).unwrap()
            }
            IBCEvent::ReceivePacket(ev) => {
                ev.height = Height::try_from(height.revision_height).unwrap()
            }
            IBCEvent::WriteAcknowledgement(ev) => {
                ev.height = Height::try_from(height.revision_height).unwrap()
            }
            IBCEvent::AcknowledgePacket(ev) => {
                ev.height = Height::try_from(height.revision_height).unwrap()
            }
            IBCEvent::TimeoutPacket(ev) => {
                ev.height = Height::try_from(height.revision_height).unwrap()
            }
            IBCEvent::CloseInitChannel(ev) => {
                ev.set_height(Height::try_from(height.revision_height).unwrap())
            }
            _ => unimplemented!(),
        }
    }
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct RawObject {
    pub height: Height,
    pub action: String,
    pub idx: usize,
    pub events: HashMap<String, Vec<String>>,
}

impl RawObject {
    pub fn new(
        height: Height,
        action: String,
        idx: usize,
        events: HashMap<String, Vec<String>>,
    ) -> RawObject {
        RawObject {
            height,
            action,
            idx,
            events,
        }
    }
}

pub fn extract_events<S: ::std::hash::BuildHasher>(
    events: &HashMap<String, Vec<String>, S>,
    action_string: &str,
) -> Result<(), BoxError> {
    if let Some(message_action) = events.get("message.action") {
        if message_action.contains(&action_string.to_owned()) {
            return Ok(());
        }
        return Err("Missing action string".into());
    }
    Err("Incorrect Event Type".into())
}

//Takes events in the form
//  "events":{
//      "connection_open_init.client_id":["testclient","testclientsec"],
//      "connection_open_init.connection_id":["ancaconnonetest","ancaconnonetestsec"],
//      "connection_open_init.counterparty_client_id":["testclientsec","testclientsecsec"],
//      "create_client.client_id":["testclientthird"],
//      "create_client.client_type":["tendermint"],
//      "message.action":["connection_open_init","create_client","connection_open_init"],
//      "message.module":["ibc_connection","ibc_client",ibc_connection"],
//      "message.sender":["cosmos187xxg4yfkypl05cqylucezpjvycj24nurvm8p9","cosmos187xxg4yfkypl05cqylucezpjvycj24nurvm8p9","cosmos187xxg4yfkypl05cqylucezpjvycj24nurvm8p9","cosmos187xxg4yfkypl05cqylucezpjvycj24nurvm8p9"],"tm.event":["Tx"],"transfer.amount":["5000stake"],"transfer.recipient":["cosmos17xpfvakm2amg962yls6f84z3kell8c5lserqta"],"tx.hash":["A9E18AE3909F22232F8DBDB1C48F2FECB260A308A2D157E8832E901D45950605"],
//      "tx.height":["35"]
// and returns:
// [{"connection_open_init", 0}, {"create_client", 0}, {"connection_open_init", 1}]
// where the number in each entry is the index in the matching events that should be used to build the event
// e.g. for the last "connection_open_init" in the result
//      "connection_open_init.client_id" -> "testclientsec"
//      "connection_open_init.connection_id" -> "ancaconnonetestsec",
//      "connection_open_init.counterparty_client_id" -> "testclientsec","testclientsecsec",
fn extract_helper(events: &HashMap<String, Vec<String>>) -> Result<Vec<(String, u32)>, String> {
    let message_action = events.get("message.action").ok_or("Incorrect Event Type")?;
    let mut val_indeces = HashMap::new();
    let mut result = Vec::new();

    for action_string in message_action {
        let idx = val_indeces
            .entry(action_string.clone())
            .or_insert_with(|| 0);
        result.push((action_string.clone(), *idx));
        *val_indeces.get_mut(action_string.as_str()).unwrap() += 1;
    }
    Ok(result)
}

pub fn get_all_events(result: RpcEvent) -> Result<Vec<(Height, IBCEvent)>, String> {
    let mut vals: Vec<(Height, IBCEvent)> = vec![];

    match &result.data {
        RpcEventData::NewBlock { block, .. } => {
            let block = block.as_ref().ok_or("missing block")?;
            vals.push((
                block.header.height,
                NewBlock::new(block.header.height).into(),
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

        "timeout_on_close_packet" => {
            object.action = "timeout_packet".to_string();
            Ok(IBCEvent::from(
                ChannelEvents::TimeoutOnClosePacket::try_from(object)?,
            ))
        }

        unknown_event => Err(unknown_event.into()),
    }
}

#[macro_export]
macro_rules! make_event {
    ($a:ident, $b:literal) => {
        #[derive(Debug, Deserialize, Serialize, Clone)]
        pub struct $a {
            pub data: std::collections::HashMap<String, Vec<String>>,
        }
        impl TryFrom<RawObject> for $a {
            type Error = BoxError;
            fn try_from(result: RawObject) -> Result<Self, Self::Error> {
                match crate::events::extract_events(&result.events, $b) {
                    Ok(()) => Ok($a {
                        data: result.events.clone(),
                    }),
                    Err(e) => Err(e),
                }
            }
        }
    };
}

#[macro_export]
macro_rules! attribute {
    ($a:ident, $b:literal) => {
        $a.events.get($b).ok_or($b)?[$a.idx].parse()?
    };
}

#[macro_export]
macro_rules! some_attribute {
    ($a:ident, $b:literal) => {
        $a.events.get($b).ok_or($b)?[$a.idx].parse().ok()
    };
}
