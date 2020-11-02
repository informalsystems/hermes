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
    ClientConsensusState {
        client_id: ClientId,
        epoch: u64,
        height: u64,
    },
    ClientConnections(ClientId),
    Connections(ConnectionId),
    Ports(PortId),
    ChannelEnds(PortId, ChannelId),
    SeqSends(PortId, ChannelId),
    SeqRecvs(PortId, ChannelId),
    SeqAcks(PortId, ChannelId),
    Commitments {
        port_id: PortId,
        channel_id: ChannelId,
        sequence: u64,
    },
    Acks {
        port_id: PortId,
        channel_id: ChannelId,
        sequence: u64,
    },
}

impl Path {
    /// Indication if the path is provable.
    pub fn is_provable(&self) -> bool {
        match &self {
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
            Path::ClientType(client_id) => write!(f, "clients/{}/clientType", client_id),
            Path::ClientState(client_id) => write!(f, "clients/{}/clientState", client_id),
            Path::ClientConsensusState {
                client_id,
                epoch,
                height,
            } => write!(
                f,
                "clients/{}/consensusState/{}-{}",
                client_id, epoch, height
            ),
            Path::ClientConnections(client_id) => write!(f, "clients/{}/connections", client_id),
            Path::Connections(connection_id) => write!(f, "connections/{}", connection_id),
            Path::Ports(port_id) => write!(f, "ports/{}", port_id),
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
            Path::Commitments {
                port_id,
                channel_id,
                sequence,
            } => write!(
                f,
                "commitments/ports/{}/channels/{}/packets/{}",
                port_id, channel_id, sequence
            ),
            Path::Acks {
                port_id,
                channel_id,
                sequence,
            } => write!(
                f,
                "acks/ports/{}/channels/{}/acknowledgements/{}",
                port_id, channel_id, sequence
            ),
        }
    }
}
