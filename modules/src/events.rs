use std::collections::HashMap;
use std::convert::TryFrom;

use anomaly::BoxError;
use serde_derive::{Deserialize, Serialize};

use tendermint::block::Height;

use crate::application::ics20_fungible_token_transfer::events as TransferEvents;
use crate::ics02_client::events as ClientEvents;
use crate::ics02_client::events::NewBlock;
use crate::ics03_connection::events as ConnectionEvents;
use crate::ics04_channel::events as ChannelEvents;
use crate::Height as ICSHeight;

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

    SendPacketChannel(ChannelEvents::SendPacket),
    ReceivePacketChannel(ChannelEvents::ReceivePacket),
    WriteAcknowledgementChannel(ChannelEvents::WriteAcknowledgement),
    AcknowledgePacketChannel(ChannelEvents::AcknowledgePacket),
    TimeoutPacketChannel(ChannelEvents::TimeoutPacket),

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

    pub fn height(&self) -> Height {
        match self {
            IBCEvent::NewBlock(bl) => bl.height,
            IBCEvent::UpdateClient(uc) => *uc.height(),
            IBCEvent::SendPacketChannel(ev) => ev.height,
            IBCEvent::ReceivePacketChannel(ev) => ev.height,
            IBCEvent::WriteAcknowledgementChannel(ev) => ev.height,
            IBCEvent::AcknowledgePacketChannel(ev) => ev.height,
            IBCEvent::TimeoutPacketChannel(ev) => ev.height,

            _ => unimplemented!(),
        }
    }

    pub fn set_height(&mut self, height: ICSHeight) {
        match self {
            IBCEvent::SendPacketChannel(ev) => {
                ev.height = Height::try_from(height.revision_height).unwrap()
            }
            IBCEvent::ReceivePacketChannel(ev) => {
                ev.height = Height::try_from(height.revision_height).unwrap()
            }
            IBCEvent::WriteAcknowledgementChannel(ev) => {
                ev.height = Height::try_from(height.revision_height).unwrap()
            }
            IBCEvent::AcknowledgePacketChannel(ev) => {
                ev.height = Height::try_from(height.revision_height).unwrap()
            }
            IBCEvent::TimeoutPacketChannel(ev) => {
                ev.height = Height::try_from(height.revision_height).unwrap()
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
