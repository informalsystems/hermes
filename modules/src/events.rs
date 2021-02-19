use std::collections::HashMap;

use anomaly::BoxError;
use serde_derive::{Deserialize, Serialize};

use crate::ics02_client::events as ClientEvents;
use crate::ics02_client::events::NewBlock;
use crate::ics03_connection::events as ConnectionEvents;
use crate::ics04_channel::events as ChannelEvents;
use crate::Height;

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

    Empty(String),      // Special event, signifying empty response
    ChainError(String), // Special event, signifying an error on CheckTx or DeliverTx
}

// This is tendermint specific
pub fn from_tx_response_event(height: Height, event: &tendermint::abci::Event) -> Option<IBCEvent> {
    // Return the first hit we find
    if let Some(mut client_res) = ClientEvents::try_from_tx(event) {
        client_res.set_height(height);
        Some(client_res)
    } else if let Some(mut conn_res) = ConnectionEvents::try_from_tx(event) {
        conn_res.set_height(height);
        Some(conn_res)
    } else if let Some(mut chan_res) = ChannelEvents::try_from_tx(event) {
        chan_res.set_height(height);
        Some(chan_res)
    } else {
        None
    }
}

impl IBCEvent {
    pub fn to_json(&self) -> String {
        serde_json::to_string(self).unwrap()
    }

    pub fn height(&self) -> &Height {
        match self {
            IBCEvent::NewBlock(bl) => bl.height(),
            IBCEvent::CreateClient(ev) => ev.height(),
            IBCEvent::UpdateClient(ev) => ev.height(),
            IBCEvent::ClientMisbehavior(ev) => ev.height(),
            IBCEvent::OpenInitConnection(ev) => ev.height(),
            IBCEvent::OpenTryConnection(ev) => ev.height(),
            IBCEvent::OpenAckConnection(ev) => ev.height(),
            IBCEvent::OpenConfirmConnection(ev) => ev.height(),
            IBCEvent::OpenInitChannel(ev) => ev.height(),
            IBCEvent::OpenTryChannel(ev) => ev.height(),
            IBCEvent::OpenAckChannel(ev) => ev.height(),
            IBCEvent::OpenConfirmChannel(ev) => ev.height(),
            IBCEvent::CloseInitChannel(ev) => ev.height(),
            IBCEvent::CloseConfirmChannel(ev) => ev.height(),
            IBCEvent::SendPacket(ev) => ev.height(),
            IBCEvent::ReceivePacket(ev) => ev.height(),
            IBCEvent::WriteAcknowledgement(ev) => ev.height(),
            IBCEvent::AcknowledgePacket(ev) => ev.height(),
            IBCEvent::TimeoutPacket(ev) => ev.height(),
            _ => unimplemented!(),
        }
    }

    pub fn set_height(&mut self, height: Height) {
        match self {
            IBCEvent::NewBlock(ev) => ev.set_height(height),
            IBCEvent::CreateClient(ev) => ev.set_height(height),
            IBCEvent::UpdateClient(ev) => ev.set_height(height),
            IBCEvent::ClientMisbehavior(ev) => ev.set_height(height),
            IBCEvent::OpenInitConnection(ev) => ev.set_height(height),
            IBCEvent::OpenTryConnection(ev) => ev.set_height(height),
            IBCEvent::OpenAckConnection(ev) => ev.set_height(height),
            IBCEvent::OpenConfirmConnection(ev) => ev.set_height(height),
            IBCEvent::OpenInitChannel(ev) => ev.set_height(height),
            IBCEvent::OpenTryChannel(ev) => ev.set_height(height),
            IBCEvent::OpenAckChannel(ev) => ev.set_height(height),
            IBCEvent::OpenConfirmChannel(ev) => ev.set_height(height),
            IBCEvent::CloseInitChannel(ev) => ev.set_height(height),
            IBCEvent::CloseConfirmChannel(ev) => ev.set_height(height),
            IBCEvent::SendPacket(ev) => ev.set_height(height),
            IBCEvent::ReceivePacket(ev) => ev.set_height(height),
            IBCEvent::WriteAcknowledgement(ev) => ev.set_height(height),
            IBCEvent::AcknowledgePacket(ev) => ev.set_height(height),
            IBCEvent::TimeoutPacket(ev) => ev.set_height(height),
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

#[macro_export]
macro_rules! make_event {
    ($a:ident, $b:literal) => {
        #[derive(Debug, Deserialize, Serialize, Clone)]
        pub struct $a {
            pub data: ::std::collections::HashMap<String, Vec<String>>,
        }
        impl ::std::convert::TryFrom<$crate::events::RawObject> for $a {
            type Error = ::anomaly::BoxError;

            fn try_from(result: $crate::events::RawObject) -> Result<Self, Self::Error> {
                match $crate::events::extract_events(&result.events, $b) {
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
