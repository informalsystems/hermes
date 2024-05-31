use std::borrow::Cow;
use std::fmt::{Display, Error as FmtError, Formatter};
use std::str::FromStr;

use flex_error::{define_error, TraceError};
use serde_derive::{Deserialize, Serialize};
use tendermint::abci;

use crate::applications::ics29_fee::error::Error as FeeError;
use crate::applications::ics29_fee::events::{DistributeFeePacket, IncentivizedPacket};
use crate::applications::ics31_icq::error::Error as QueryPacketError;
use crate::applications::ics31_icq::events::CrossChainQueryPacket;
use crate::core::ics02_client::error as client_error;
use crate::core::ics02_client::events as ClientEvents;
use crate::core::ics02_client::events::NewBlock;
use crate::core::ics03_connection::error as connection_error;
use crate::core::ics03_connection::events as ConnectionEvents;
use crate::core::ics03_connection::events::Attributes as ConnectionAttributes;
use crate::core::ics04_channel::error as channel_error;
use crate::core::ics04_channel::events::Attributes as ChannelAttributes;
use crate::core::ics04_channel::events::{self as ChannelEvents, UpgradeAttributes};
use crate::core::ics04_channel::packet::Packet;
use crate::core::ics24_host::error::ValidationError;
use crate::timestamp::ParseTimestampError;
use crate::utils::pretty::PrettySlice;

define_error! {
    Error {
        Height
            | _ | { "error parsing height" },

        Parse
            [ ValidationError ]
            | _ | { "parse error" },

        Client
            [ client_error::Error ]
            | _ | { "ICS02 client error" },

        Connection
            [ connection_error::Error ]
            | _ | { "connection error" },

        Channel
            [ channel_error::Error ]
            | _ | { "channel error" },

        Fee
            [ FeeError ]
            | _ | { "fee error" },

        CrossChainQuery
            [ QueryPacketError ]
            | _ | { "cross chain query error" },

        Timestamp
            [ ParseTimestampError ]
            | _ | { "error parsing timestamp" },

        MissingKey
            { key: String }
            | e | { format_args!("missing event key {}", e.key) },

        Decode
            [ TraceError<prost::DecodeError> ]
            | _ | { "error decoding protobuf" },

        InvalidPacketData
            { data: String }
            | e | { format_args!("error decoding hex-encoded packet data: {}", e.data) },

        InvalidPacketAck
            { ack: String }
            | e | { format_args!("error decoding hex-encoded packet ack: {}", e.ack) },

        MissingActionString
            | _ | { "missing action string" },

        IncorrectEventType
            { event: String }
            | e | { format_args!("incorrect event type: {}", e.event) },

        MalformedModuleEvent
            { event: ModuleEvent }
            | e | { format_args!("module event cannot use core event types: {:?}", e.event) },

        UnsupportedAbciEvent
            {event_type: String}
            |e| { format_args!("Unable to parse abci event type '{}' into IbcEvent", e.event_type)}
    }
}

/// Events whose data is not included in the app state and must be extracted using tendermint RPCs
/// (i.e. /tx_search or /block_search)
#[derive(Debug, Clone, Deserialize, Serialize)]
pub enum WithBlockDataType {
    CreateClient,
    UpdateClient,
    SendPacket,
    WriteAck,
}

impl WithBlockDataType {
    pub fn as_str(&self) -> &'static str {
        match *self {
            WithBlockDataType::CreateClient => "create_client",
            WithBlockDataType::UpdateClient => "update_client",
            WithBlockDataType::SendPacket => "send_packet",
            WithBlockDataType::WriteAck => "write_acknowledgement",
        }
    }
}

const NEW_BLOCK_EVENT: &str = "new_block";
const EMPTY_EVENT: &str = "empty";
const CHAIN_ERROR_EVENT: &str = "chain_error";
const APP_MODULE_EVENT: &str = "app_module";
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
/// Channel upgrade event types
const CHANNEL_UPGRADE_INIT_EVENT: &str = "channel_upgrade_init";
const CHANNEL_UPGRADE_TRY_EVENT: &str = "channel_upgrade_try";
const CHANNEL_UPGRADE_ACK_EVENT: &str = "channel_upgrade_ack";
const CHANNEL_UPGRADE_CONFIRM_EVENT: &str = "channel_upgrade_confirm";
const CHANNEL_UPGRADE_OPEN_EVENT: &str = "channel_upgrade_open";
const CHANNEL_UPGRADE_CANCEL_EVENT: &str = "channel_upgrade_cancelled";
const CHANNEL_UPGRADE_TIMEOUT_EVENT: &str = "channel_upgrade_timeout";
const CHANNEL_UPGRADE_ERROR_EVENT: &str = "channel_upgrade_error";
/// Packet event types
const SEND_PACKET_EVENT: &str = "send_packet";
const RECEIVE_PACKET_EVENT: &str = "receive_packet";
const WRITE_ACK_EVENT: &str = "write_acknowledgement";
const ACK_PACKET_EVENT: &str = "acknowledge_packet";
const TIMEOUT_EVENT: &str = "timeout_packet";
const TIMEOUT_ON_CLOSE_EVENT: &str = "timeout_packet_on_close";
const INCENTIVIZED_PACKET_EVENT: &str = "incentivized_ibc_packet";
/// CrossChainQuery event type
const CROSS_CHAIN_QUERY_PACKET_EVENT: &str = "cross_chain_query";
/// Distribution fee event type
const DISTRIBUTION_FEE_PACKET_EVENT: &str = "distribute_fee";

/// Events types
#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
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
    UpgradeInitChannel,
    UpgradeTryChannel,
    UpgradeAckChannel,
    UpgradeConfirmChannel,
    UpgradeOpenChannel,
    UpgradeCancelChannel,
    UpgradeTimeoutChannel,
    UpgradeErrorChannel,
    SendPacket,
    ReceivePacket,
    WriteAck,
    AckPacket,
    Timeout,
    TimeoutOnClose,
    IncentivizedPacket,
    CrossChainQuery,
    AppModule,
    Empty,
    ChainError,
    DistributionFee,
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
            IbcEventType::UpgradeInitChannel => CHANNEL_UPGRADE_INIT_EVENT,
            IbcEventType::UpgradeTryChannel => CHANNEL_UPGRADE_TRY_EVENT,
            IbcEventType::UpgradeAckChannel => CHANNEL_UPGRADE_ACK_EVENT,
            IbcEventType::UpgradeConfirmChannel => CHANNEL_UPGRADE_CONFIRM_EVENT,
            IbcEventType::UpgradeOpenChannel => CHANNEL_UPGRADE_OPEN_EVENT,
            IbcEventType::UpgradeCancelChannel => CHANNEL_UPGRADE_CANCEL_EVENT,
            IbcEventType::UpgradeTimeoutChannel => CHANNEL_UPGRADE_TIMEOUT_EVENT,
            IbcEventType::UpgradeErrorChannel => CHANNEL_UPGRADE_ERROR_EVENT,
            IbcEventType::SendPacket => SEND_PACKET_EVENT,
            IbcEventType::ReceivePacket => RECEIVE_PACKET_EVENT,
            IbcEventType::WriteAck => WRITE_ACK_EVENT,
            IbcEventType::AckPacket => ACK_PACKET_EVENT,
            IbcEventType::Timeout => TIMEOUT_EVENT,
            IbcEventType::TimeoutOnClose => TIMEOUT_ON_CLOSE_EVENT,
            IbcEventType::IncentivizedPacket => INCENTIVIZED_PACKET_EVENT,
            IbcEventType::CrossChainQuery => CROSS_CHAIN_QUERY_PACKET_EVENT,
            IbcEventType::AppModule => APP_MODULE_EVENT,
            IbcEventType::Empty => EMPTY_EVENT,
            IbcEventType::ChainError => CHAIN_ERROR_EVENT,
            IbcEventType::DistributionFee => DISTRIBUTION_FEE_PACKET_EVENT,
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
            CHANNEL_UPGRADE_INIT_EVENT => Ok(IbcEventType::UpgradeInitChannel),
            CHANNEL_UPGRADE_TRY_EVENT => Ok(IbcEventType::UpgradeTryChannel),
            CHANNEL_UPGRADE_ACK_EVENT => Ok(IbcEventType::UpgradeAckChannel),
            CHANNEL_UPGRADE_CONFIRM_EVENT => Ok(IbcEventType::UpgradeConfirmChannel),
            CHANNEL_UPGRADE_OPEN_EVENT => Ok(IbcEventType::UpgradeOpenChannel),
            CHANNEL_UPGRADE_CANCEL_EVENT => Ok(IbcEventType::UpgradeCancelChannel),
            CHANNEL_UPGRADE_TIMEOUT_EVENT => Ok(IbcEventType::UpgradeTimeoutChannel),
            CHANNEL_UPGRADE_ERROR_EVENT => Ok(IbcEventType::UpgradeErrorChannel),
            SEND_PACKET_EVENT => Ok(IbcEventType::SendPacket),
            RECEIVE_PACKET_EVENT => Ok(IbcEventType::ReceivePacket),
            WRITE_ACK_EVENT => Ok(IbcEventType::WriteAck),
            ACK_PACKET_EVENT => Ok(IbcEventType::AckPacket),
            TIMEOUT_EVENT => Ok(IbcEventType::Timeout),
            TIMEOUT_ON_CLOSE_EVENT => Ok(IbcEventType::TimeoutOnClose),
            INCENTIVIZED_PACKET_EVENT => Ok(IbcEventType::IncentivizedPacket),
            CROSS_CHAIN_QUERY_PACKET_EVENT => Ok(IbcEventType::CrossChainQuery),
            EMPTY_EVENT => Ok(IbcEventType::Empty),
            CHAIN_ERROR_EVENT => Ok(IbcEventType::ChainError),
            DISTRIBUTION_FEE_PACKET_EVENT => Ok(IbcEventType::DistributionFee),
            // from_str() for `APP_MODULE_EVENT` MUST fail because a `ModuleEvent`'s type isn't constant
            _ => Err(Error::incorrect_event_type(s.to_string())),
        }
    }
}

/// Events created by the IBC component of a chain, destined for a relayer.
#[derive(Debug, Clone, Serialize)]
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
    UpgradeInitChannel(ChannelEvents::UpgradeInit),
    UpgradeTryChannel(ChannelEvents::UpgradeTry),
    UpgradeAckChannel(ChannelEvents::UpgradeAck),
    UpgradeConfirmChannel(ChannelEvents::UpgradeConfirm),
    UpgradeOpenChannel(ChannelEvents::UpgradeOpen),
    UpgradeCancelChannel(ChannelEvents::UpgradeCancel),
    UpgradeTimeoutChannel(ChannelEvents::UpgradeTimeout),
    UpgradeErrorChannel(ChannelEvents::UpgradeError),

    SendPacket(ChannelEvents::SendPacket),
    ReceivePacket(ChannelEvents::ReceivePacket),
    WriteAcknowledgement(ChannelEvents::WriteAcknowledgement),
    AcknowledgePacket(ChannelEvents::AcknowledgePacket),
    TimeoutPacket(ChannelEvents::TimeoutPacket),
    TimeoutOnClosePacket(ChannelEvents::TimeoutOnClosePacket),

    IncentivizedPacket(IncentivizedPacket),
    CrossChainQueryPacket(CrossChainQueryPacket),

    DistributeFeePacket(DistributeFeePacket),

    AppModule(ModuleEvent),

    ChainError(String), // Special event, signifying an error on CheckTx or DeliverTx
}

impl Display for IbcEvent {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        match self {
            IbcEvent::NewBlock(ev) => write!(f, "NewBlock({})", ev.height),

            IbcEvent::CreateClient(ev) => write!(f, "CreateClient({ev})"),
            IbcEvent::UpdateClient(ev) => write!(f, "UpdateClient({ev})"),
            IbcEvent::UpgradeClient(ev) => write!(f, "UpgradeClient({ev})"),
            IbcEvent::ClientMisbehaviour(ev) => write!(f, "ClientMisbehaviour({ev})"),

            IbcEvent::OpenInitConnection(ev) => write!(f, "OpenInitConnection({ev})"),
            IbcEvent::OpenTryConnection(ev) => write!(f, "OpenTryConnection({ev})"),
            IbcEvent::OpenAckConnection(ev) => write!(f, "OpenAckConnection({ev})"),
            IbcEvent::OpenConfirmConnection(ev) => write!(f, "OpenConfirmConnection({ev})"),

            IbcEvent::OpenInitChannel(ev) => write!(f, "OpenInitChannel({ev})"),
            IbcEvent::OpenTryChannel(ev) => write!(f, "OpenTryChannel({ev})"),
            IbcEvent::OpenAckChannel(ev) => write!(f, "OpenAckChannel({ev})"),
            IbcEvent::OpenConfirmChannel(ev) => write!(f, "OpenConfirmChannel({ev})"),
            IbcEvent::CloseInitChannel(ev) => write!(f, "CloseInitChannel({ev})"),
            IbcEvent::CloseConfirmChannel(ev) => write!(f, "CloseConfirmChannel({ev})"),
            IbcEvent::UpgradeInitChannel(ev) => write!(f, "UpgradeInitChannel({ev})"),
            IbcEvent::UpgradeTryChannel(ev) => write!(f, "UpgradeTryChannel({ev})"),
            IbcEvent::UpgradeAckChannel(ev) => write!(f, "UpgradeAckChannel({ev})"),
            IbcEvent::UpgradeConfirmChannel(ev) => write!(f, "UpgradeConfirmChannel({ev})"),
            IbcEvent::UpgradeOpenChannel(ev) => write!(f, "UpgradeOpenChannel({ev})"),
            IbcEvent::UpgradeCancelChannel(ev) => write!(f, "UpgradeCancelChannel({ev})"),
            IbcEvent::UpgradeTimeoutChannel(ev) => write!(f, "UpgradeTimeoutChannel({ev})"),
            IbcEvent::UpgradeErrorChannel(ev) => write!(f, "UpgradeErrorChannel({ev})"),

            IbcEvent::SendPacket(ev) => write!(f, "SendPacket({ev})"),
            IbcEvent::ReceivePacket(ev) => write!(f, "ReceivePacket({ev})"),
            IbcEvent::WriteAcknowledgement(ev) => write!(f, "WriteAcknowledgement({ev})"),
            IbcEvent::AcknowledgePacket(ev) => write!(f, "AcknowledgePacket({ev})"),
            IbcEvent::TimeoutPacket(ev) => write!(f, "TimeoutPacket({ev})"),
            IbcEvent::TimeoutOnClosePacket(ev) => write!(f, "TimeoutOnClosePacket({ev})"),

            IbcEvent::IncentivizedPacket(ev) => write!(f, "IncenvitizedPacket({ev:?}"),
            IbcEvent::CrossChainQueryPacket(ev) => write!(f, "CrosschainPacket({ev:?})"),

            IbcEvent::DistributeFeePacket(ev) => write!(f, "DistributionFeePacket({ev:?})"),

            IbcEvent::AppModule(ev) => write!(f, "AppModule({ev})"),

            IbcEvent::ChainError(ev) => write!(f, "ChainError({ev})"),
        }
    }
}

impl IbcEvent {
    pub fn to_json(&self) -> String {
        match serde_json::to_string(self) {
            Ok(value) => value,
            Err(_) => format!("{self:?}"), // Fallback to debug printing
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
            IbcEvent::UpgradeInitChannel(_) => IbcEventType::UpgradeInitChannel,
            IbcEvent::UpgradeTryChannel(_) => IbcEventType::UpgradeTryChannel,
            IbcEvent::UpgradeAckChannel(_) => IbcEventType::UpgradeAckChannel,
            IbcEvent::UpgradeConfirmChannel(_) => IbcEventType::UpgradeConfirmChannel,
            IbcEvent::UpgradeOpenChannel(_) => IbcEventType::UpgradeOpenChannel,
            IbcEvent::UpgradeCancelChannel(_) => IbcEventType::UpgradeCancelChannel,
            IbcEvent::UpgradeTimeoutChannel(_) => IbcEventType::UpgradeTimeoutChannel,
            IbcEvent::UpgradeErrorChannel(_) => IbcEventType::UpgradeErrorChannel,
            IbcEvent::SendPacket(_) => IbcEventType::SendPacket,
            IbcEvent::ReceivePacket(_) => IbcEventType::ReceivePacket,
            IbcEvent::WriteAcknowledgement(_) => IbcEventType::WriteAck,
            IbcEvent::AcknowledgePacket(_) => IbcEventType::AckPacket,
            IbcEvent::TimeoutPacket(_) => IbcEventType::Timeout,
            IbcEvent::TimeoutOnClosePacket(_) => IbcEventType::TimeoutOnClose,
            IbcEvent::IncentivizedPacket(_) => IbcEventType::IncentivizedPacket,
            IbcEvent::CrossChainQueryPacket(_) => IbcEventType::CrossChainQuery,
            IbcEvent::DistributeFeePacket(_) => IbcEventType::DistributionFee,
            IbcEvent::AppModule(_) => IbcEventType::AppModule,
            IbcEvent::ChainError(_) => IbcEventType::ChainError,
        }
    }

    pub fn channel_attributes(self) -> Option<ChannelAttributes> {
        match self {
            IbcEvent::OpenInitChannel(ev) => Some(ev.into()),
            IbcEvent::OpenTryChannel(ev) => Some(ev.into()),
            IbcEvent::OpenAckChannel(ev) => Some(ev.into()),
            IbcEvent::OpenConfirmChannel(ev) => Some(ev.into()),
            _ => None,
        }
    }

    pub fn channel_upgrade_attributes(self) -> Option<UpgradeAttributes> {
        match self {
            IbcEvent::UpgradeInitChannel(ev) => Some(ev.into()),
            IbcEvent::UpgradeTryChannel(ev) => Some(ev.into()),
            IbcEvent::UpgradeAckChannel(ev) => Some(ev.into()),
            IbcEvent::UpgradeConfirmChannel(ev) => Some(ev.into()),
            IbcEvent::UpgradeOpenChannel(ev) => Some(ev.into()),
            IbcEvent::UpgradeCancelChannel(ev) => Some(ev.into()),
            IbcEvent::UpgradeTimeoutChannel(ev) => Some(ev.into()),
            IbcEvent::UpgradeErrorChannel(ev) => Some(ev.into()),
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

    pub fn cross_chain_query_packet(&self) -> Option<&CrossChainQueryPacket> {
        match self {
            IbcEvent::CrossChainQueryPacket(ev) => Some(ev),
            _ => None,
        }
    }

    pub fn ack(&self) -> Option<&[u8]> {
        match self {
            IbcEvent::WriteAcknowledgement(ev) => Some(&ev.ack),
            _ => None,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct InvalidModuleId;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Deserialize, Serialize)]
pub struct ModuleId(String);

impl ModuleId {
    pub fn new(s: Cow<'_, str>) -> Result<Self, InvalidModuleId> {
        if !s.trim().is_empty() && s.chars().all(char::is_alphanumeric) {
            Ok(Self(s.into_owned()))
        } else {
            Err(InvalidModuleId)
        }
    }
}

impl Display for ModuleId {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "{}", self.0)
    }
}

impl FromStr for ModuleId {
    type Err = InvalidModuleId;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::new(Cow::Borrowed(s))
    }
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct ModuleEvent {
    pub kind: String,
    pub module_name: ModuleId,
    pub attributes: Vec<ModuleEventAttribute>,
}

impl Display for ModuleEvent {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(
            f,
            "ModuleEvent {{ kind: {}, module_name: {}, attributes: {} }}",
            self.kind,
            self.module_name,
            PrettySlice(&self.attributes)
        )
    }
}

impl TryFrom<ModuleEvent> for abci::Event {
    type Error = Error;

    fn try_from(event: ModuleEvent) -> Result<Self, Self::Error> {
        if IbcEventType::from_str(event.kind.as_str()).is_ok() {
            return Err(Error::malformed_module_event(event));
        }

        let attributes = event.attributes.into_iter().map(Into::into).collect();
        Ok(Self {
            kind: event.kind,
            attributes,
        })
    }
}

impl From<ModuleEvent> for IbcEvent {
    fn from(e: ModuleEvent) -> Self {
        IbcEvent::AppModule(e)
    }
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct ModuleEventAttribute {
    pub key: String,
    pub value: String,
}

impl Display for ModuleEventAttribute {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(
            f,
            "ModuleEventAttribute {{ key: {}, value: {} }}",
            self.key, self.value
        )
    }
}

impl<K: ToString, V: ToString> From<(K, V)> for ModuleEventAttribute {
    fn from((k, v): (K, V)) -> Self {
        Self {
            key: k.to_string(),
            value: v.to_string(),
        }
    }
}

impl From<ModuleEventAttribute> for abci::EventAttribute {
    fn from(attr: ModuleEventAttribute) -> Self {
        (attr.key, attr.value).into()
    }
}
