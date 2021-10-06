use crate::prelude::*;
use core::fmt;
use core::str::FromStr;
use flex_error::{define_error, TraceError};
use prost::alloc::fmt::Formatter;
use serde_derive::{Deserialize, Serialize};
use tendermint::abci::Event as AbciEvent;

use crate::ics02_client::error as client_error;
use crate::ics02_client::events as ClientEvents;
use crate::ics02_client::events::NewBlock;
use crate::ics02_client::height::HeightError;
use crate::ics03_connection::events as ConnectionEvents;
use crate::ics03_connection::events::Attributes as ConnectionAttributes;
use crate::ics04_channel::error as channel_error;
use crate::ics04_channel::events as ChannelEvents;
use crate::ics04_channel::events::Attributes as ChannelAttributes;
use crate::ics04_channel::packet::Packet;
use crate::ics24_host::error::ValidationError;
use crate::timestamp::ParseTimestampError;
use crate::Height;

define_error! {
    Error {
        Height
            [ HeightError ]
            | _ | { "error parsing height" },

        Parse
            [ ValidationError ]
            | _ | { "parse error" },

        Client
            [ client_error::Error ]
            | _ | { "ICS02 client error" },

        Channel
            [ channel_error::Error ]
            | _ | { "channel error" },

        Timestamp
            [ ParseTimestampError ]
            | _ | { "error parsing timestamp" },

        MissingKey
            { key: String }
            | e | { format_args!("missing event key {}", e.key) },

        Decode
            [ TraceError<prost::DecodeError> ]
            | _ | { "error decoding protobuf" },

        SubtleEncoding
            [ TraceError<subtle_encoding::Error> ]
            | _ | { "error decoding hex" },

        MissingActionString
            | _ | { "Missing action string" },

        IncorrectEventType
            { event: String }
            | e | {
                format_args!("Incorrect Event Type {}",
                    e.event)
            },
    }
}

const NEW_BLOCK_EVENT: &str = "new_block";
const EMPTY_EVENT: &str = "empty";
const CHAIN_ERROR_EVENT: &str = "chain_error";
/// Client event types
const CREATE_CLIENT_EVENT: &str = "create_client";
const UPDATE_CLIENT_EVENT: &str = "update_client";
const CLIENT_MISBEHAVIOUR_EVENT: &str = "client_misbehaviour";
const UPGRADE_CLIENT_EVENT: &str = "upgrade_client";
/// Connection event types
const CONNECTION_INIT_EVENT: &str = "connection_open_init";
const CONNECTION_TRY_EVENT: &str = "connection_open_try";
const CONNECTION_ACK_EVENT: &str = "connection_open_ack";
const CONNECTION_CONFIRM_EVENT: &str = "connection_open_confirm";
/// Channel event types
const CHANNEL_OPEN_INIT_EVENT: &str = "channel_open_init";
const CHANNEL_OPEN_TRY_EVENT: &str = "channel_open_try";
const CHANNEL_OPEN_ACK_EVENT: &str = "channel_open_ack";
const CHANNEL_OPEN_CONFIRM_EVENT: &str = "channel_open_confirm";
const CHANNEL_CLOSE_INIT_EVENT: &str = "channel_close_init";
const CHANNEL_CLOSE_CONFIRM_EVENT: &str = "channel_close_confirm";
/// Packet event types
const SEND_PACKET_EVENT: &str = "send_packet";
const RECEIVE_PACKET_EVENT: &str = "receive_packet";
const WRITE_ACK_EVENT: &str = "write_acknowledgement";
const ACK_PACKET_EVENT: &str = "acknowledge_packet";
const TIMEOUT_EVENT: &str = "timeout_packet";
const TIMEOUT_ON_CLOSE_EVENT: &str = "timeout_packet_on_close";

/// Events types
#[derive(Debug, Clone, Deserialize, Serialize)]
pub enum IbcEventType {
    NewBlock,
    CreateClient,
    UpdateClient,
    UpgradeClient,
    ClientMisbehaviour,
    OpenInitConnection,
    OpenTryConnection,
    OpenAckConnection,
    OpenConfirmConnection,
    OpenInitChannel,
    OpenTryChannel,
    OpenAckChannel,
    OpenConfirmChannel,
    CloseInitChannel,
    CloseConfirmChannel,
    SendPacket,
    ReceivePacket,
    WriteAck,
    AckPacket,
    Timeout,
    TimeoutOnClose,
    Empty,
    ChainError,
}

impl IbcEventType {
    pub fn as_str(&self) -> &'static str {
        match *self {
            IbcEventType::NewBlock => NEW_BLOCK_EVENT,
            IbcEventType::CreateClient => CREATE_CLIENT_EVENT,
            IbcEventType::UpdateClient => UPDATE_CLIENT_EVENT,
            IbcEventType::UpgradeClient => UPGRADE_CLIENT_EVENT,
            IbcEventType::ClientMisbehaviour => CLIENT_MISBEHAVIOUR_EVENT,
            IbcEventType::OpenInitConnection => CONNECTION_INIT_EVENT,
            IbcEventType::OpenTryConnection => CONNECTION_TRY_EVENT,
            IbcEventType::OpenAckConnection => CONNECTION_ACK_EVENT,
            IbcEventType::OpenConfirmConnection => CONNECTION_CONFIRM_EVENT,
            IbcEventType::OpenInitChannel => CHANNEL_OPEN_INIT_EVENT,
            IbcEventType::OpenTryChannel => CHANNEL_OPEN_TRY_EVENT,
            IbcEventType::OpenAckChannel => CHANNEL_OPEN_ACK_EVENT,
            IbcEventType::OpenConfirmChannel => CHANNEL_OPEN_CONFIRM_EVENT,
            IbcEventType::CloseInitChannel => CHANNEL_CLOSE_INIT_EVENT,
            IbcEventType::CloseConfirmChannel => CHANNEL_CLOSE_CONFIRM_EVENT,
            IbcEventType::SendPacket => SEND_PACKET_EVENT,
            IbcEventType::ReceivePacket => RECEIVE_PACKET_EVENT,
            IbcEventType::WriteAck => WRITE_ACK_EVENT,
            IbcEventType::AckPacket => ACK_PACKET_EVENT,
            IbcEventType::Timeout => TIMEOUT_EVENT,
            IbcEventType::TimeoutOnClose => TIMEOUT_ON_CLOSE_EVENT,
            IbcEventType::Empty => EMPTY_EVENT,
            IbcEventType::ChainError => CHAIN_ERROR_EVENT,
        }
    }
}

impl FromStr for IbcEventType {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            NEW_BLOCK_EVENT => Ok(IbcEventType::NewBlock),
            CREATE_CLIENT_EVENT => Ok(IbcEventType::CreateClient),
            UPDATE_CLIENT_EVENT => Ok(IbcEventType::UpdateClient),
            UPGRADE_CLIENT_EVENT => Ok(IbcEventType::UpgradeClient),
            CLIENT_MISBEHAVIOUR_EVENT => Ok(IbcEventType::ClientMisbehaviour),
            CONNECTION_INIT_EVENT => Ok(IbcEventType::OpenInitConnection),
            CONNECTION_TRY_EVENT => Ok(IbcEventType::OpenTryConnection),
            CONNECTION_ACK_EVENT => Ok(IbcEventType::OpenAckConnection),
            CONNECTION_CONFIRM_EVENT => Ok(IbcEventType::OpenConfirmConnection),
            CHANNEL_OPEN_INIT_EVENT => Ok(IbcEventType::OpenInitChannel),
            CHANNEL_OPEN_TRY_EVENT => Ok(IbcEventType::OpenTryChannel),
            CHANNEL_OPEN_ACK_EVENT => Ok(IbcEventType::OpenAckChannel),
            CHANNEL_OPEN_CONFIRM_EVENT => Ok(IbcEventType::OpenConfirmChannel),
            CHANNEL_CLOSE_INIT_EVENT => Ok(IbcEventType::CloseInitChannel),
            CHANNEL_CLOSE_CONFIRM_EVENT => Ok(IbcEventType::CloseConfirmChannel),
            SEND_PACKET_EVENT => Ok(IbcEventType::SendPacket),
            RECEIVE_PACKET_EVENT => Ok(IbcEventType::ReceivePacket),
            WRITE_ACK_EVENT => Ok(IbcEventType::WriteAck),
            ACK_PACKET_EVENT => Ok(IbcEventType::AckPacket),
            TIMEOUT_EVENT => Ok(IbcEventType::Timeout),
            TIMEOUT_ON_CLOSE_EVENT => Ok(IbcEventType::TimeoutOnClose),
            EMPTY_EVENT => Ok(IbcEventType::Empty),
            CHAIN_ERROR_EVENT => Ok(IbcEventType::ChainError),
            _ => Err(Error::incorrect_event_type(s.to_string())),
        }
    }
}

/// Events created by the IBC component of a chain, destined for a relayer.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub enum IbcEvent {
    NewBlock(NewBlock),

    CreateClient(ClientEvents::CreateClient),
    UpdateClient(ClientEvents::UpdateClient),
    UpgradeClient(ClientEvents::UpgradeClient),
    ClientMisbehaviour(ClientEvents::ClientMisbehaviour),

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

/// For use in debug messages
pub struct PrettyEvents<'a>(pub &'a [IbcEvent]);
impl<'a> fmt::Display for PrettyEvents<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "events:")?;
        for v in self.0 {
            writeln!(f, "\t{}", v)?;
        }
        Ok(())
    }
}

impl fmt::Display for IbcEvent {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            IbcEvent::NewBlock(ev) => write!(f, "NewBlock({})", ev.height),

            IbcEvent::CreateClient(ev) => write!(f, "CreateClientEv({})", ev),
            IbcEvent::UpdateClient(ev) => write!(f, "UpdateClientEv({})", ev),
            IbcEvent::UpgradeClient(ev) => write!(f, "UpgradeClientEv({:?})", ev),
            IbcEvent::ClientMisbehaviour(ev) => write!(f, "ClientMisbehaviourEv({:?})", ev),

            IbcEvent::OpenInitConnection(ev) => write!(f, "OpenInitConnectionEv({:?})", ev),
            IbcEvent::OpenTryConnection(ev) => write!(f, "OpenTryConnectionEv({:?})", ev),
            IbcEvent::OpenAckConnection(ev) => write!(f, "OpenAckConnectionEv({:?})", ev),
            IbcEvent::OpenConfirmConnection(ev) => write!(f, "OpenConfirmConnectionEv({:?})", ev),

            IbcEvent::OpenInitChannel(ev) => write!(f, "OpenInitChannelEv({:?})", ev),
            IbcEvent::OpenTryChannel(ev) => write!(f, "OpenTryChannelEv({:?})", ev),
            IbcEvent::OpenAckChannel(ev) => write!(f, "OpenAckChannelEv({:?})", ev),
            IbcEvent::OpenConfirmChannel(ev) => write!(f, "OpenConfirmChannelEv({:?})", ev),
            IbcEvent::CloseInitChannel(ev) => write!(f, "CloseInitChannelEv({})", ev),
            IbcEvent::CloseConfirmChannel(ev) => write!(f, "CloseConfirmChannelEv({:?})", ev),

            IbcEvent::SendPacket(ev) => write!(f, "SendPacketEv({})", ev),
            IbcEvent::ReceivePacket(ev) => write!(f, "ReceivePacketEv({})", ev),
            IbcEvent::WriteAcknowledgement(ev) => write!(f, "WriteAcknowledgementEv({})", ev),
            IbcEvent::AcknowledgePacket(ev) => write!(f, "AcknowledgePacketEv({})", ev),
            IbcEvent::TimeoutPacket(ev) => write!(f, "TimeoutPacketEv({})", ev),
            IbcEvent::TimeoutOnClosePacket(ev) => write!(f, "TimeoutOnClosePacketEv({})", ev),

            IbcEvent::Empty(ev) => write!(f, "EmptyEv({})", ev),
            IbcEvent::ChainError(ev) => write!(f, "ChainErrorEv({})", ev),
        }
    }
}

// This is tendermint specific
pub fn from_tx_response_event(height: Height, event: &tendermint::abci::Event) -> Option<IbcEvent> {
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

//

impl IbcEvent {
    pub fn to_json(&self) -> String {
        match serde_json::to_string(self) {
            Ok(value) => value,
            Err(_) => format!("{:?}", self), // Fallback to debug printing
        }
    }

    pub fn height(&self) -> Height {
        match self {
            IbcEvent::NewBlock(bl) => bl.height(),
            IbcEvent::CreateClient(ev) => ev.height(),
            IbcEvent::UpdateClient(ev) => ev.height(),
            IbcEvent::ClientMisbehaviour(ev) => ev.height(),
            IbcEvent::OpenInitConnection(ev) => ev.height(),
            IbcEvent::OpenTryConnection(ev) => ev.height(),
            IbcEvent::OpenAckConnection(ev) => ev.height(),
            IbcEvent::OpenConfirmConnection(ev) => ev.height(),
            IbcEvent::OpenInitChannel(ev) => ev.height(),
            IbcEvent::OpenTryChannel(ev) => ev.height(),
            IbcEvent::OpenAckChannel(ev) => ev.height(),
            IbcEvent::OpenConfirmChannel(ev) => ev.height(),
            IbcEvent::CloseInitChannel(ev) => ev.height(),
            IbcEvent::CloseConfirmChannel(ev) => ev.height(),
            IbcEvent::SendPacket(ev) => ev.height(),
            IbcEvent::ReceivePacket(ev) => ev.height(),
            IbcEvent::WriteAcknowledgement(ev) => ev.height(),
            IbcEvent::AcknowledgePacket(ev) => ev.height(),
            IbcEvent::TimeoutPacket(ev) => ev.height(),
            _ => unimplemented!(),
        }
    }

    pub fn set_height(&mut self, height: Height) {
        match self {
            IbcEvent::NewBlock(ev) => ev.set_height(height),
            IbcEvent::CreateClient(ev) => ev.set_height(height),
            IbcEvent::UpdateClient(ev) => ev.set_height(height),
            IbcEvent::UpgradeClient(ev) => ev.set_height(height),
            IbcEvent::ClientMisbehaviour(ev) => ev.set_height(height),
            IbcEvent::OpenInitConnection(ev) => ev.set_height(height),
            IbcEvent::OpenTryConnection(ev) => ev.set_height(height),
            IbcEvent::OpenAckConnection(ev) => ev.set_height(height),
            IbcEvent::OpenConfirmConnection(ev) => ev.set_height(height),
            IbcEvent::OpenInitChannel(ev) => ev.set_height(height),
            IbcEvent::OpenTryChannel(ev) => ev.set_height(height),
            IbcEvent::OpenAckChannel(ev) => ev.set_height(height),
            IbcEvent::OpenConfirmChannel(ev) => ev.set_height(height),
            IbcEvent::CloseInitChannel(ev) => ev.set_height(height),
            IbcEvent::CloseConfirmChannel(ev) => ev.set_height(height),
            IbcEvent::SendPacket(ev) => ev.set_height(height),
            IbcEvent::ReceivePacket(ev) => ev.set_height(height),
            IbcEvent::WriteAcknowledgement(ev) => ev.set_height(height),
            IbcEvent::AcknowledgePacket(ev) => ev.set_height(height),
            IbcEvent::TimeoutPacket(ev) => ev.set_height(height),
            _ => unimplemented!(),
        }
    }

    pub fn event_type(&self) -> IbcEventType {
        match self {
            IbcEvent::NewBlock(_) => IbcEventType::NewBlock,
            IbcEvent::CreateClient(_) => IbcEventType::CreateClient,
            IbcEvent::UpdateClient(_) => IbcEventType::UpdateClient,
            IbcEvent::ClientMisbehaviour(_) => IbcEventType::ClientMisbehaviour,
            IbcEvent::UpgradeClient(_) => IbcEventType::UpgradeClient,
            IbcEvent::OpenInitConnection(_) => IbcEventType::OpenInitConnection,
            IbcEvent::OpenTryConnection(_) => IbcEventType::OpenTryConnection,
            IbcEvent::OpenAckConnection(_) => IbcEventType::OpenAckConnection,
            IbcEvent::OpenConfirmConnection(_) => IbcEventType::OpenConfirmConnection,
            IbcEvent::OpenInitChannel(_) => IbcEventType::OpenInitChannel,
            IbcEvent::OpenTryChannel(_) => IbcEventType::OpenTryChannel,
            IbcEvent::OpenAckChannel(_) => IbcEventType::OpenAckChannel,
            IbcEvent::OpenConfirmChannel(_) => IbcEventType::OpenConfirmChannel,
            IbcEvent::CloseInitChannel(_) => IbcEventType::CloseInitChannel,
            IbcEvent::CloseConfirmChannel(_) => IbcEventType::CloseConfirmChannel,
            IbcEvent::SendPacket(_) => IbcEventType::SendPacket,
            IbcEvent::ReceivePacket(_) => IbcEventType::ReceivePacket,
            IbcEvent::WriteAcknowledgement(_) => IbcEventType::WriteAck,
            IbcEvent::AcknowledgePacket(_) => IbcEventType::AckPacket,
            IbcEvent::TimeoutPacket(_) => IbcEventType::Timeout,
            IbcEvent::TimeoutOnClosePacket(_) => IbcEventType::TimeoutOnClose,
            IbcEvent::Empty(_) => IbcEventType::Empty,
            IbcEvent::ChainError(_) => IbcEventType::ChainError,
        }
    }

    pub fn abci_event(&self) -> Option<AbciEvent> {
        match self {
            IbcEvent::CreateClient(ev) => Some(ev.clone().into()),
            IbcEvent::UpdateClient(ev) => Some(ev.clone().into()),
            IbcEvent::UpgradeClient(ev) => Some(ev.clone().into()),
            IbcEvent::ClientMisbehaviour(ev) => Some(ev.clone().into()),
            IbcEvent::OpenInitConnection(ev) => Some(ev.clone().into()),
            IbcEvent::OpenTryConnection(ev) => Some(ev.clone().into()),
            IbcEvent::OpenAckConnection(ev) => Some(ev.clone().into()),
            IbcEvent::OpenConfirmConnection(ev) => Some(ev.clone().into()),
            IbcEvent::OpenInitChannel(ev) => Some(ev.clone().into()),
            IbcEvent::OpenTryChannel(ev) => Some(ev.clone().into()),
            IbcEvent::OpenAckChannel(ev) => Some(ev.clone().into()),
            IbcEvent::OpenConfirmChannel(ev) => Some(ev.clone().into()),
            IbcEvent::CloseInitChannel(ev) => Some(ev.clone().into()),
            IbcEvent::CloseConfirmChannel(ev) => Some(ev.clone().into()),
            IbcEvent::SendPacket(ev) => Some(ev.clone().into()),
            IbcEvent::WriteAcknowledgement(ev) => Some(ev.clone().into()),
            IbcEvent::AcknowledgePacket(ev) => Some(ev.clone().into()),
            IbcEvent::TimeoutPacket(ev) => Some(ev.clone().into()),
            _ => None,
        }
    }

    pub fn channel_attributes(&self) -> Option<&ChannelAttributes> {
        match self {
            IbcEvent::OpenInitChannel(ev) => Some(ev.attributes()),
            IbcEvent::OpenTryChannel(ev) => Some(ev.attributes()),
            IbcEvent::OpenAckChannel(ev) => Some(ev.attributes()),
            IbcEvent::OpenConfirmChannel(ev) => Some(ev.attributes()),
            _ => None,
        }
    }

    pub fn connection_attributes(&self) -> Option<&ConnectionAttributes> {
        match self {
            IbcEvent::OpenInitConnection(ev) => Some(ev.attributes()),
            IbcEvent::OpenTryConnection(ev) => Some(ev.attributes()),
            IbcEvent::OpenAckConnection(ev) => Some(ev.attributes()),
            IbcEvent::OpenConfirmConnection(ev) => Some(ev.attributes()),
            _ => None,
        }
    }

    pub fn packet(&self) -> Option<&Packet> {
        match self {
            IbcEvent::SendPacket(ev) => Some(&ev.packet),
            IbcEvent::ReceivePacket(ev) => Some(&ev.packet),
            IbcEvent::WriteAcknowledgement(ev) => Some(&ev.packet),
            IbcEvent::AcknowledgePacket(ev) => Some(&ev.packet),
            IbcEvent::TimeoutPacket(ev) => Some(&ev.packet),
            IbcEvent::TimeoutOnClosePacket(ev) => Some(&ev.packet),
            _ => None,
        }
    }

    pub fn ack(&self) -> Option<Vec<u8>> {
        match self {
            IbcEvent::WriteAcknowledgement(ev) => Some(ev.ack.clone()),
            _ => None,
        }
    }
}
