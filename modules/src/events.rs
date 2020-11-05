use crate::ics02_client::events as ClientEvents;
use crate::ics02_client::events::NewBlock;
use crate::ics03_connection::events as ConnectionEvents;
use crate::ics04_channel::events as ChannelEvents;
use crate::ics20_fungible_token_transfer::events as TransferEvents;

use tendermint_rpc::event::{Event as RpcEvent, EventData as RpcEventData};

use anomaly::BoxError;
use serde_derive::{Deserialize, Serialize};
use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};
use tendermint::block::Height;

use tracing::warn;

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

    SendPacketChannel(ChannelEvents::SendPacket),
    ReceivePacketChannel(ChannelEvents::ReceivePacket),
    AcknowledgePacketChannel(ChannelEvents::AcknowledgePacket),
    CleanupPacketChannel(ChannelEvents::CleanupPacket),
    TimeoutPacketChannel(ChannelEvents::TimeoutPacket),

    TimeoutTransfer(TransferEvents::Timeout),
    PacketTransfer(TransferEvents::Packet),
    ChannelClosedTransfer(TransferEvents::ChannelClosed),
}

impl IBCEvent {
    pub fn to_json(&self) -> String {
        serde_json::to_string(self).unwrap()
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

pub fn get_all_events(result: RpcEvent) -> Result<Vec<IBCEvent>, String> {
    let mut vals: Vec<IBCEvent> = vec![];

    match &result.data {
        RpcEventData::NewBlock { block, .. } => {
            let block = block.as_ref().ok_or("missing block")?;
            vals.push(NewBlock::new(block.header().height).into());
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
                let event = build_event(RawObject::new(
                    height,
                    action.0,
                    action.1 as usize,
                    events.clone(),
                ));

                match event {
                    Ok(event) => vals.push(event),
                    Err(e) => warn!("error while building event {}", e.to_string()),
                }
            }
        }
        _ => {}
    }
    Ok(vals)
}

pub fn build_event(object: RawObject) -> Result<IBCEvent, BoxError> {
    match object.action.as_str() {
        "create_client" => Ok(IBCEvent::from(ClientEvents::CreateClient::try_from(
            object,
        )?)),
        "update_client" => Ok(IBCEvent::from(ClientEvents::UpdateClient::try_from(
            object,
        )?)),

        "connection_open_init" => Ok(IBCEvent::from(ConnectionEvents::OpenInit::try_from(
            object,
        )?)),
        "connection_open_try" => Ok(IBCEvent::from(ConnectionEvents::OpenTry::try_from(object)?)),
        "connection_open_ack" => Ok(IBCEvent::from(ConnectionEvents::OpenAck::try_from(object)?)),
        "connection_open_confirm" => Ok(IBCEvent::from(ConnectionEvents::OpenConfirm::try_from(
            object,
        )?)),

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

        // send_packet
        "transfer" => Ok(IBCEvent::from(ChannelEvents::SendPacket::try_from(object)?)),
        // recv_packet
        "ics04/opaque" => Ok(IBCEvent::from(ChannelEvents::ReceivePacket::try_from(
            object,
        )?)),
        // acknowledge_packet
        // needs these changes in cosmos-sdk
        //        --- a/x/ibc/04-channel/types/msgs.go
        //        +++ b/x/ibc/04-channel/types/msgs.go
        //    @@ -511,5 +511,5 @@ func (msg MsgAcknowledgement) GetSigners() []sdk.AccAddress {
        //
        //        // Type implements sdk.Msg
        //        func (msg MsgAcknowledgement) Type() string {
        //            -       return "ics04/opaque"
        //            +       return "ics04/acknowledge"
        //        }
        "ics04/acknowledge" => Ok(IBCEvent::from(ChannelEvents::AcknowledgePacket::try_from(
            object,
        )?)),
        //timeout_packet
        "ics04/timeout" => Ok(IBCEvent::from(ChannelEvents::TimeoutPacket::try_from(
            object,
        )?)),

        // TODO not clear what the message.action for this is
        "cleanup_packet" => Ok(IBCEvent::from(ChannelEvents::CleanupPacket::try_from(
            object,
        )?)),

        _ => Err("Incorrect Event Type".into()),
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
