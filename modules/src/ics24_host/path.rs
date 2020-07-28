/// Path-space as listed in ICS-024
/// https://github.com/cosmos/ics/tree/master/spec/ics-024-host-requirements#path-space
/// Some of these are implemented in other ICSs, but ICS-024 has a nice summary table.
use crate::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};
use std::fmt::{Display, Formatter, Result};

/// IBC Query Path is hard-coded
pub const IBC_QUERY_PATH: &str = "store/ibc/key";

/// The Path enum abstracts out the different sub-paths
pub enum Path {
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

impl Path {
    /// Indication if the path is provable.
    pub fn is_provable(&self) -> bool {
        match &self {
            Path::ClientState(_) => false,
            Path::ClientConnections(_) => false,
            Path::Ports(_) => false,
            _ => true,
        }
    }

    /// into_bytes implementation
    pub fn into_bytes(self) -> Vec<u8> {
        self.to_string().into_bytes()
    }
}

/// The Display trait adds the `.to_string()` method to the Path struct
/// This is where the different path strings are constructed
impl Display for Path {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match &self {
            Path::ClientType(id) => write!(f, "clients/{}/clientType", id),
            Path::ClientState(id) => write!(f, "clients/{}/clientState", id),
            Path::ConsensusState(id, height) => {
                write!(f, "clients/{}/consensusState/{}", id, height)
            }
            Path::ClientConnections(id) => write!(f, "clients/{}/connections", id),
            Path::Connections(id) => write!(f, "connections/{}", id),
            Path::Ports(id) => write!(f, "ports/{}", id),
            Path::ChannelEnds(port_id, channel_id) => {
                write!(f, "channelEnds/ports/{}/channels/{}", port_id, channel_id)
            }
            Path::SeqSends(port_id, channel_id) => write!(
                f,
                "seqSends/ports/{}/channels/{}/nextSequenceSend",
                port_id, channel_id
            ),
            Path::SeqRecvs(port_id, channel_id) => write!(
                f,
                "seqRecvs/ports/{}/channels/{}/nextSequenceRecv",
                port_id, channel_id
            ),
            Path::SeqAcks(port_id, channel_id) => write!(
                f,
                "seqAcks/ports/{}/channels/{}/nextSequenceAck",
                port_id, channel_id
            ),
            Path::Commitments(port_id, channel_id, seq) => write!(
                f,
                "commitments/ports/{}/channels/{}/packets/{}",
                port_id, channel_id, seq
            ),
            Path::Acks(port_id, channel_id, seq) => write!(
                f,
                "acks/ports/{}/channels/{}/acknowledgements/{}",
                port_id, channel_id, seq
            ),
        }
    }
}
