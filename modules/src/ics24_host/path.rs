/// Path-space as listed in ICS-024
/// https://github.com/cosmos/ics/tree/master/spec/ics-024-host-requirements#path-space
/// Some of these are implemented in other ICSs, but ICS-024 has a nice summary table.
use crate::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use std::fmt::{Display, Formatter, Result};

/// IBC Query Path is hard-coded
pub const IBC_QUERY_PATH: &str = "store/ibc/key";

/// The Data enum abstracts out the different Path types
pub enum Data {
    ClientType(ClientId),
    ClientState(ClientId),
    ConsensusState(ClientId, u64),
    ClientConnections(ClientId),
    Connections(ConnectionId),
    Ports(PortId),
    ChannelEnds(PortId, ChannelId),
    SeqSends(PortId, ChannelId),
    SeqRecvs(PortId, ChannelId),
    SeqAcks(PortId, ChannelId),
    Commitments(PortId, ChannelId, u64),
    Acks(PortId, ChannelId, u64),
}

impl Data {
    /// Indication if the data type is provable.
    pub fn is_provable(&self) -> bool {
        match &self {
            Data::ClientState(_) => false,
            Data::ClientConnections(_) => false,
            Data::Ports(_) => false,
            _ => true,
        }
    }
}

/// The Path struct converts the Data enum into the Paths defined by the ICS
pub struct Path {
    data: Data,
}

/// The Display trait adds the `.to_string()` method to the RawData struct
/// This is where the different path strings are constructed
impl Display for Path {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match &self.data {
            Data::ClientType(id) => write!(f, "clients/{}/clientType", id),
            Data::ClientState(id) => write!(f, "clients/{}/clientState", id),
            Data::ConsensusState(id, height) => {
                write!(f, "clients/{}/consensusState/{}", id, height)
            }
            Data::ClientConnections(id) => write!(f, "clients/{}/connections", id),
            Data::Connections(id) => write!(f, "connections/{}", id),
            Data::Ports(id) => write!(f, "ports/{}", id),
            Data::ChannelEnds(port_id, channel_id) => {
                write!(f, "channelEnds/ports/{}/channels/{}", port_id, channel_id)
            }
            Data::SeqSends(port_id, channel_id) => write!(
                f,
                "seqSends/ports/{}/channels/{}/nextSequenceSend",
                port_id, channel_id
            ),
            Data::SeqRecvs(port_id, channel_id) => write!(
                f,
                "seqRecvs/ports/{}/channels/{}/nextSequenceRecv",
                port_id, channel_id
            ),
            Data::SeqAcks(port_id, channel_id) => write!(
                f,
                "seqAcks/ports/{}/channels/{}/nextSequenceAck",
                port_id, channel_id
            ),
            Data::Commitments(port_id, channel_id, seq) => write!(
                f,
                "commitments/ports/{}/channels/{}/packets/{}",
                port_id, channel_id, seq
            ),
            Data::Acks(port_id, channel_id, seq) => write!(
                f,
                "acks/ports/{}/channels/{}/acknowledgements/{}",
                port_id, channel_id, seq
            ),
        }
    }
}

impl Path {
    /// into_bytes implementation
    pub fn into_bytes(self) -> Vec<u8> {
        self.to_string().into_bytes()
    }
}

/// Easily construct a new Path using the From trait
impl From<Data> for Path {
    fn from(data: Data) -> Self {
        Path { data }
    }
}
