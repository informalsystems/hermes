use crate::ics02_client::events as ClientEvents;
use crate::ics03_connection::events as ConnectionEvents;
use crate::ics04_channel::events as ChannelEvents;
use crate::ics20_fungible_token_transfer::events as TransferEvents;
use std::convert::TryFrom;
use tendermint::rpc::event_listener::Event;

#[derive(Debug)]
pub enum IBCEvent{
    CreateClient(ClientEvents::CreateClient),
    UpdateClient(ClientEvents::UpdateClient),
    ClientMisbehavior(ClientEvents::ClientMisbehavior),
    OpenInitConnection(ConnectionEvents::OpenInit),
    OpenTryConnection(ConnectionEvents::OpenTry),
    OpenAckConnection(ConnectionEvents::OpenAck),
    OpenConfirmConnection(ConnectionEvents::OpenConfirm),
    SendPacketChannel(ChannelEvents::SendPacket),
    RecievePacketChannel(ChannelEvents::RecievePacket),
    AcknowledgePacketChannel(ChannelEvents::AcknowledgePacket),
    CleanupPacketChannel(ChannelEvents::CleanupPacket),
    TimeoutPacketChannel(ChannelEvents::TimeoutPacket),
    TimeoutTransferEvent(TransferEvents::Timeout),
    PacketTransfer(TransferEvents::Packet),
    ChannelClosedTranfer(TransferEvents::ChannelClosed),
}

impl IBCEvent {
    pub fn get_all_events(event: Event) -> Vec<IBCEvents> {
        let mut vals: Vec<IBCEvents> = vec![];
        if let Ok(ev) = ClientEvents::CreateClient::try_from(&event) {
            vals.push(IBCEvents::from(ev));
        }
        if let Ok(ev) = ClientEvents::UpdateClient::try_from(&event) {
            vals.push(IBCEvents::from(ev));
        }
        if let Ok(ev) = ClientEvents::ClientMisbehavior::try_from(&event) {
            vals.push(IBCEvents::from(ev));
        }
        if let Ok(ev) = ConnectionEvents::OpenInit::try_from(&event) {
            vals.push(IBCEvents::from(ev));
        }
        if let Ok(ev) = ConnectionEvents::OpenTry::try_from(&event) {
            vals.push(IBCEvents::from(ev));
        }
        if let Ok(ev) = ConnectionEvents::OpenAck::try_from(&event) {
            vals.push(IBCEvents::from(ev));
        }
        if let Ok(ev) = ConnectionEvents::OpenConfirm::try_from(&event) {
            vals.push(IBCEvents::from(ev));
        }
        if let Ok(ev) = ChannelEvents::SendPacket::try_from(&event) {
            vals.push(IBCEvents::from(ev));
        }
        if let Ok(ev) = ChannelEvents::RecievePacket::try_from(&event) {
            vals.push(IBCEvents::from(ev));
        }
        if let Ok(ev) = ChannelEvents::AcknowledgePacket::try_from(&event) {
            vals.push(IBCEvents::from(ev));
        }
        if let Ok(ev) = ChannelEvents::CleanupPacket::try_from(&event) {
            vals.push(IBCEvents::from(ev));
        }
        if let Ok(ev) = ChannelEvents::TimeoutPacket::try_from(&event) {
            vals.push(IBCEvents::from(ev));
        }
        if let Ok(ev) = TransferEvents::Timeout::try_from(&event) {
            vals.push(IBCEvents::from(ev));
        }
        if let Ok(ev) = TransferEvents::Packet::try_from(&event) {
            vals.push(IBCEvents::from(ev));
        }
        if let Ok(ev) = TransferEvents::ChannelClosed::try_from(&event) {
            vals.push(IBCEvents::from(ev));
        }
        return vals;
    }
}

impl From<TransferEvents::Timeout> for IBCEvents {
    fn from(v: TransferEvents::Timeout) -> Self {
        IBCEvents::TimeoutTransferEvent(v)
    }
}

impl From<ChannelEvents::TimeoutPacket> for IBCEvents {
    fn from(v: ChannelEvents::TimeoutPacket) -> Self {
        IBCEvents::TimeoutPacketChannel(v)
    }
}

impl From<ChannelEvents::CleanupPacket> for IBCEvents {
    fn from(v: ChannelEvents::CleanupPacket) -> Self {
        IBCEvents::CleanupPacketChannel(v)
    }
}

impl From<ChannelEvents::AcknowledgePacket> for IBCEvents {
    fn from(v: ChannelEvents::AcknowledgePacket) -> Self {
        IBCEvents::AcknowledgePacketChannel(v)
    }
}

impl From<ChannelEvents::RecievePacket> for IBCEvents {
    fn from(v: ChannelEvents::RecievePacket) -> Self {
        IBCEvents::RecievePacketChannel(v)
    }
}

impl From<ChannelEvents::SendPacket> for IBCEvents {
    fn from(v: ChannelEvents::SendPacket) -> Self {
        IBCEvents::SendPacketChannel(v)
    }
}

impl From<ConnectionEvents::OpenConfirm> for IBCEvents {
    fn from(v: ConnectionEvents::OpenConfirm) -> Self {
        IBCEvents::OpenConfirmConnection(v)
    }
}

impl From<ConnectionEvents::OpenAck> for IBCEvents {
    fn from(v: ConnectionEvents::OpenAck) -> Self {
        IBCEvents::OpenAckConnection(v)
    }
}

impl From<ConnectionEvents::OpenTry> for IBCEvents {
    fn from(v: ConnectionEvents::OpenTry) -> Self {
        IBCEvents::OpenTryConnection(v)
    }
}

impl From<ConnectionEvents::OpenInit> for IBCEvents {
    fn from(v: ConnectionEvents::OpenInit) -> Self {
        IBCEvents::OpenInitConnection(v)
    }
}

impl From<ClientEvents::ClientMisbehavior> for IBCEvents {
    fn from(v: ClientEvents::ClientMisbehavior) -> Self {
        IBCEvents::ClientMisbehavior(v)
    }
}

impl From<ClientEvents::UpdateClient> for IBCEvents {
    fn from(v: ClientEvents::UpdateClient) -> Self {
        IBCEvents::UpdateClient(v)
    }
}

impl From<ClientEvents::CreateClient> for IBCEvents {
    fn from(v: ClientEvents::CreateClient) -> Self {
        IBCEvents::CreateClient(v)
    }
}

impl From<TransferEvents::ChannelClosed> for IBCEvents {
    fn from(v: TransferEvents::ChannelClosed) -> Self {
        IBCEvents::ChannelClosedTranfer(v)
    }
}

impl From<TransferEvents::Packet> for IBCEvents {
    fn from(v: TransferEvents::Packet) -> Self {
        IBCEvents::PacketTransfer(v)
    }
}

#[macro_export]
macro_rules! make_event {
    ($a:ident, $b:literal, $c:literal) => {
        #[derive(Debug, Deserialize, Serialize, Clone)]
        pub struct $a {
            events: std::collections::HashMap<String, Vec<String>>,
        }
        impl TryFrom<&Event> for $a {
            type Error = &'static str;
            fn try_from(event: &Event) -> Result<Self, Self::Error> {
                match event {
                    Event::JsonRPCTransctionResult { ref data } => Ok($a {
                        events: data.extract_events($b, $c)?.clone(),
                    }),
                    Event::GenericJSONEvent { .. } => {
                        Err("Expected JSON representing a $a, got wrong type")?
                    }

                    Event::GenericStringEvent { .. } => Err("Generic event is not of $a"),
                }
            }
        }
    };
}
