use crate::prelude::*;

/// Path-space as listed in ICS-024
/// https://github.com/cosmos/ibc/tree/master/spec/ics-024-host-requirements#path-space
/// Some of these are implemented in other ICSs, but ICS-024 has a nice summary table.
///
use core::fmt::{self, Display, Formatter};
use core::str::FromStr;

use crate::ics04_channel::packet::Sequence;
use crate::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};

use flex_error::define_error;

/// ABCI Query path for the IBC sub-store
pub const IBC_QUERY_PATH: &str = "store/ibc/key";

/// ABCI Query path for the upgrade sub-store
/// ## Note: This is SDK/Tendermint specific!
pub const SDK_UPGRADE_QUERY_PATH: &str = "store/upgrade/key";

/// ABCI client upgrade keys
/// - The key identifying the upgraded IBC state within the upgrade sub-store
const UPGRADED_IBC_STATE: &str = "upgradedIBCState";
///- The key identifying the upgraded client state
const UPGRADED_CLIENT_STATE: &str = "upgradedClient";
/// - The key identifying the upgraded consensus state
const UPGRADED_CLIENT_CONSENSUS_STATE: &str = "upgradedConsState";

/// The Path enum abstracts out the different sub-paths.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
        sequence: Sequence,
    },
    Acks {
        port_id: PortId,
        channel_id: ChannelId,
        sequence: Sequence,
    },
    Receipts {
        port_id: PortId,
        channel_id: ChannelId,
        sequence: Sequence,
    },
    Upgrade(ClientUpgradePath),
}

/// Paths that are specific for client upgrades.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ClientUpgradePath {
    UpgradedClientState(u64),
    UpgradedClientConsensusState(u64),
}

/// Sub-paths which are not part of the specification, but are still
/// useful to represent for parsing purposes.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum SubPath {
    Channels(ChannelId),
    Sequences(Sequence),
}

impl Path {
    /// Indication if the path is provable.
    pub fn is_provable(&self) -> bool {
        !matches!(&self, Path::ClientConnections(_) | Path::Ports(_))
    }

    /// into_bytes implementation
    pub fn into_bytes(self) -> Vec<u8> {
        self.to_string().into_bytes()
    }
}

/// The Display trait adds the `.to_string()` method to the Path struct.
/// This is where the different path strings are constructed.
impl Display for Path {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match &self {
            Path::ClientType(client_id) => write!(f, "clients/{}/clientType", client_id),
            Path::ClientState(client_id) => write!(f, "clients/{}/clientState", client_id),
            Path::ClientConsensusState {
                client_id,
                epoch,
                height,
            } => write!(
                f,
                "clients/{}/consensusStates/{}-{}",
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
                "nextSequenceSend/ports/{}/channels/{}",
                port_id, channel_id
            ),
            Path::SeqRecvs(port_id, channel_id) => write!(
                f,
                "nextSequenceRecv/ports/{}/channels/{}",
                port_id, channel_id
            ),
            Path::SeqAcks(port_id, channel_id) => write!(
                f,
                "nextSequenceAck/ports/{}/channels/{}",
                port_id, channel_id
            ),
            Path::Commitments {
                port_id,
                channel_id,
                sequence,
            } => write!(
                f,
                "commitments/ports/{}/channels/{}/sequences/{}",
                port_id, channel_id, sequence
            ),
            Path::Acks {
                port_id,
                channel_id,
                sequence,
            } => write!(
                f,
                "acks/ports/{}/channels/{}/sequences/{}",
                port_id, channel_id, sequence
            ),
            Path::Receipts {
                port_id,
                channel_id,
                sequence,
            } => write!(
                f,
                "receipts/ports/{}/channels/{}/sequences/{}",
                port_id, channel_id, sequence
            ),
            Path::Upgrade(ClientUpgradePath::UpgradedClientState(height)) => write!(
                f,
                "{}/{}/{}",
                UPGRADED_IBC_STATE, height, UPGRADED_CLIENT_STATE
            ),
            Path::Upgrade(ClientUpgradePath::UpgradedClientConsensusState(height)) => write!(
                f,
                "{}/{}/{}",
                UPGRADED_IBC_STATE, height, UPGRADED_CLIENT_CONSENSUS_STATE
            ),
        }
    }
}

define_error! {
    #[derive(Eq, PartialEq)]
    PathError {
        ParseFailure
            { path: String }
            | e | { format!("'{}' could not be parsed into a Path", e.path) },
    }
}

/// The FromStr trait allows paths encoded as strings to be parsed into Paths.
impl FromStr for Path {
    type Err = PathError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let components: Vec<&str> = s.split('/').collect();

        parse_client_paths(&components)
            .or_else(|| parse_connections(&components))
            .or_else(|| parse_ports(&components))
            .or_else(|| parse_channel_ends(&components))
            .or_else(|| parse_seqs(&components))
            .or_else(|| parse_commitments(&components))
            .or_else(|| parse_acks(&components))
            .or_else(|| parse_receipts(&components))
            .or_else(|| parse_upgrades(&components))
            .ok_or_else(|| PathError::parse_failure(s.to_string()))
    }
}

fn parse_client_paths(components: &[&str]) -> Option<Path> {
    let first = match components.first() {
        Some(f) => *f,
        None => return None,
    };

    if first != "clients" {
        return None;
    }

    let client_id = match ClientId::from_str(components[1]) {
        Ok(s) => s,
        Err(_) => return None,
    };

    if components.len() == 3 {
        match components[2] {
            "clientType" => Some(Path::ClientType(client_id)),
            "clientState" => Some(Path::ClientState(client_id)),
            "connections" => Some(Path::ClientConnections(client_id)),
            _ => None,
        }
    } else if components.len() == 4 {
        if "consensusStates" != components[2] {
            return None;
        }

        let epoch_height = match components.last() {
            Some(eh) => *eh,
            None => return None,
        };

        let epoch_height: Vec<&str> = epoch_height.split('-').collect();

        if epoch_height.len() != 2 {
            return None;
        }

        let epoch = epoch_height[0];
        let height = epoch_height[1];

        let epoch = match epoch.parse::<u64>() {
            Ok(ep) => ep,
            Err(_) => return None,
        };

        let height = match height.parse::<u64>() {
            Ok(h) => h,
            Err(_) => return None,
        };

        Some(Path::ClientConsensusState {
            client_id,
            epoch,
            height,
        })
    } else {
        None
    }
}

fn parse_connections(components: &[&str]) -> Option<Path> {
    if components.len() != 2 {
        return None;
    }

    let first = match components.first() {
        Some(f) => *f,
        None => return None,
    };

    if first != "connections" {
        return None;
    }

    let connection_id = match components.last() {
        Some(c) => *c,
        None => return None,
    };

    let connection_id = match ConnectionId::from_str(connection_id) {
        Ok(c) => c,
        Err(_) => return None,
    };

    Some(Path::Connections(connection_id))
}

fn parse_ports(components: &[&str]) -> Option<Path> {
    if components.len() != 2 {
        return None;
    }

    let first = match components.first() {
        Some(f) => *f,
        None => return None,
    };

    if first != "ports" {
        return None;
    }

    let port_id = match components.last() {
        Some(p) => *p,
        None => return None,
    };

    let port_id = match PortId::from_str(port_id) {
        Ok(p) => p,
        Err(_) => return None,
    };

    Some(Path::Ports(port_id))
}

fn parse_channels(components: &[&str]) -> Option<SubPath> {
    if components.len() != 2 {
        return None;
    }

    let first = match components.first() {
        Some(f) => *f,
        None => return None,
    };

    if first != "channels" {
        return None;
    }

    let channel_id = match components.last() {
        Some(c) => *c,
        None => return None,
    };

    let channel_id = match ChannelId::from_str(channel_id) {
        Ok(c) => c,
        Err(_) => return None,
    };

    Some(SubPath::Channels(channel_id))
}

fn parse_sequences(components: &[&str]) -> Option<SubPath> {
    if components.len() != 2 {
        return None;
    }

    let first = match components.first() {
        Some(f) => *f,
        None => return None,
    };

    if first != "sequences" {
        return None;
    }

    let sequence_number = match components.last() {
        Some(s) => *s,
        None => return None,
    };

    match Sequence::from_str(sequence_number) {
        Ok(seq) => Some(SubPath::Sequences(seq)),
        Err(_) => None,
    }
}

fn parse_channel_ends(components: &[&str]) -> Option<Path> {
    if components.len() != 5 {
        return None;
    }

    let first = match components.first() {
        Some(f) => *f,
        None => return None,
    };

    if first != "channelEnds" {
        return None;
    }

    let port = parse_ports(&components[1..=2]);
    let channel = parse_channels(&components[3..=4]);

    let port_id = if let Some(Path::Ports(port_id)) = port {
        port_id
    } else {
        return None;
    };

    let channel_id = if let Some(SubPath::Channels(channel_id)) = channel {
        channel_id
    } else {
        return None;
    };

    Some(Path::ChannelEnds(port_id, channel_id))
}

fn parse_seqs(components: &[&str]) -> Option<Path> {
    if components.len() != 5 {
        return None;
    }

    let first = match components.first() {
        Some(f) => *f,
        None => return None,
    };

    let port = parse_ports(&components[1..=2]);
    let channel = parse_channels(&components[3..=4]);

    let port_id = if let Some(Path::Ports(port_id)) = port {
        port_id
    } else {
        return None;
    };

    let channel_id = if let Some(SubPath::Channels(channel_id)) = channel {
        channel_id
    } else {
        return None;
    };

    match first {
        "nextSequenceSend" => Some(Path::SeqSends(port_id, channel_id)),
        "nextSequenceRecv" => Some(Path::SeqRecvs(port_id, channel_id)),
        "nextSequenceAck" => Some(Path::SeqAcks(port_id, channel_id)),
        _ => None,
    }
}

fn parse_commitments(components: &[&str]) -> Option<Path> {
    if components.len() != 7 {
        return None;
    }

    let first = match components.first() {
        Some(f) => *f,
        None => return None,
    };

    if first != "commitments" {
        return None;
    }

    let port = parse_ports(&components[1..=2]);
    let channel = parse_channels(&components[3..=4]);
    let sequence = parse_sequences(&components[5..]);

    let port_id = if let Some(Path::Ports(port_id)) = port {
        port_id
    } else {
        return None;
    };

    let channel_id = if let Some(SubPath::Channels(channel_id)) = channel {
        channel_id
    } else {
        return None;
    };

    let sequence = if let Some(SubPath::Sequences(seq)) = sequence {
        seq
    } else {
        return None;
    };

    Some(Path::Commitments {
        port_id,
        channel_id,
        sequence,
    })
}

fn parse_acks(components: &[&str]) -> Option<Path> {
    if components.len() != 7 {
        return None;
    }

    let first = match components.first() {
        Some(f) => *f,
        None => return None,
    };

    if first != "acks" {
        return None;
    }

    let port = parse_ports(&components[1..=2]);
    let channel = parse_channels(&components[3..=4]);
    let sequence = parse_sequences(&components[5..]);

    let port_id = if let Some(Path::Ports(port_id)) = port {
        port_id
    } else {
        return None;
    };

    let channel_id = if let Some(SubPath::Channels(channel_id)) = channel {
        channel_id
    } else {
        return None;
    };

    let sequence = if let Some(SubPath::Sequences(seq)) = sequence {
        seq
    } else {
        return None;
    };

    Some(Path::Acks {
        port_id,
        channel_id,
        sequence,
    })
}

fn parse_receipts(components: &[&str]) -> Option<Path> {
    if components.len() != 7 {
        return None;
    }

    let first = match components.first() {
        Some(f) => *f,
        None => return None,
    };

    if first != "receipts" {
        return None;
    }

    let port = parse_ports(&components[1..=2]);
    let channel = parse_channels(&components[3..=4]);
    let sequence = parse_sequences(&components[5..]);

    let port_id = if let Some(Path::Ports(port_id)) = port {
        port_id
    } else {
        return None;
    };

    let channel_id = if let Some(SubPath::Channels(channel_id)) = channel {
        channel_id
    } else {
        return None;
    };

    let sequence = if let Some(SubPath::Sequences(seq)) = sequence {
        seq
    } else {
        return None;
    };

    Some(Path::Receipts {
        port_id,
        channel_id,
        sequence,
    })
}

fn parse_upgrades(components: &[&str]) -> Option<Path> {
    if components.len() != 3 {
        return None;
    }

    let first = match components.first() {
        Some(f) => *f,
        None => return None,
    };

    if first != UPGRADED_IBC_STATE {
        return None;
    }

    let last = match components.last() {
        Some(l) => *l,
        None => return None,
    };

    let height = match components[1].parse::<u64>() {
        Ok(h) => h,
        Err(_) => return None,
    };

    match last {
        UPGRADED_CLIENT_STATE => Some(Path::Upgrade(ClientUpgradePath::UpgradedClientState(
            height,
        ))),
        UPGRADED_CLIENT_CONSENSUS_STATE => Some(Path::Upgrade(
            ClientUpgradePath::UpgradedClientConsensusState(height),
        )),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::str::FromStr;

    #[test]
    fn invalid_path_doesnt_parse() {
        let invalid_path = Path::from_str("clients/clientType");

        assert!(invalid_path.is_err());
    }

    #[test]
    fn test_parse_client_paths_fn() {
        let path = "clients/07-tendermint-0/clientType";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_client_paths(&components),
            Some(Path::ClientType(ClientId::default()))
        );

        let path = "clients/07-tendermint-0/clientState";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_client_paths(&components),
            Some(Path::ClientState(ClientId::default()))
        );

        let path = "clients/07-tendermint-0/consensusStates/15-31";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_client_paths(&components),
            Some(Path::ClientConsensusState {
                client_id: ClientId::default(),
                epoch: 15,
                height: 31,
            })
        );
    }

    #[test]
    fn client_type_path_parses() {
        let path = "clients/07-tendermint-0/clientType";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(path.unwrap(), Path::ClientType(ClientId::default()),);
    }

    #[test]
    fn client_state_path_parses() {
        let path = "clients/07-tendermint-0/clientState";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(path.unwrap(), Path::ClientState(ClientId::default()));
    }

    #[test]
    fn client_consensus_state_path_parses() {
        let path = "clients/07-tendermint-0/consensusStates/15-31";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(
            path.unwrap(),
            Path::ClientConsensusState {
                client_id: ClientId::default(),
                epoch: 15,
                height: 31,
            }
        );
    }

    #[test]
    fn client_connections_path_parses() {
        let path = "clients/07-tendermint-0/connections";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(path.unwrap(), Path::ClientConnections(ClientId::default()));
    }

    #[test]
    fn test_parse_connections_fn() {
        let path = "connections/connection-0";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_connections(&components),
            Some(Path::Connections(ConnectionId::new(0))),
        );
    }

    #[test]
    fn connections_path_parses() {
        let path = "connections/connection-0";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(path.unwrap(), Path::Connections(ConnectionId::new(0)));
    }

    #[test]
    fn test_parse_ports_fn() {
        let path = "ports/defaultPort";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_ports(&components),
            Some(Path::Ports(PortId::default())),
        );
    }

    #[test]
    fn ports_path_parses() {
        let path = "ports/defaultPort";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(path.unwrap(), Path::Ports(PortId::default()));
    }

    #[test]
    fn test_parse_channels_fn() {
        let path = "channels/channel-0";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_channels(&components),
            Some(SubPath::Channels(ChannelId::default())),
        );
    }

    #[test]
    fn channels_path_doesnt_parse() {
        let path = "channels/channel-0";
        let path = Path::from_str(path);

        assert!(path.is_err());
    }

    #[test]
    fn test_parse_sequences_fn() {
        let path = "sequences/0";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_sequences(&components),
            Some(SubPath::Sequences(Sequence::default()))
        );
    }

    #[test]
    fn sequences_path_doesnt_parse() {
        let path = "sequences/0";
        let path = Path::from_str(path);

        assert!(path.is_err());
    }

    #[test]
    fn test_parse_channel_ends_fn() {
        let path = "channelEnds/ports/defaultPort/channels/channel-0";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_channel_ends(&components),
            Some(Path::ChannelEnds(PortId::default(), ChannelId::default())),
        );
    }

    #[test]
    fn channel_ends_path_parses() {
        let path = "channelEnds/ports/defaultPort/channels/channel-0";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(
            path.unwrap(),
            Path::ChannelEnds(PortId::default(), ChannelId::default()),
        );
    }

    #[test]
    fn test_parse_seqs_fn() {
        let path = "nextSequenceSend/ports/defaultPort/channels/channel-0";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_seqs(&components),
            Some(Path::SeqSends(PortId::default(), ChannelId::default())),
        );

        let path = "nextSequenceRecv/ports/defaultPort/channels/channel-0";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_seqs(&components),
            Some(Path::SeqRecvs(PortId::default(), ChannelId::default())),
        );

        let path = "nextSequenceAck/ports/defaultPort/channels/channel-0";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_seqs(&components),
            Some(Path::SeqAcks(PortId::default(), ChannelId::default())),
        );
    }

    #[test]
    fn sequence_send_path_parses() {
        let path = "nextSequenceSend/ports/defaultPort/channels/channel-0";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(
            path.unwrap(),
            Path::SeqSends(PortId::default(), ChannelId::default()),
        );
    }

    #[test]
    fn sequence_recv_path_parses() {
        let path = "nextSequenceRecv/ports/defaultPort/channels/channel-0";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(
            path.unwrap(),
            Path::SeqRecvs(PortId::default(), ChannelId::default()),
        );
    }

    #[test]
    fn sequence_ack_path_parses() {
        let path = "nextSequenceAck/ports/defaultPort/channels/channel-0";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(
            path.unwrap(),
            Path::SeqAcks(PortId::default(), ChannelId::default()),
        );
    }

    #[test]
    fn test_parse_commitments_fn() {
        let path = "commitments/ports/defaultPort/channels/channel-0/sequences/0";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_commitments(&components),
            Some(Path::Commitments {
                port_id: PortId::default(),
                channel_id: ChannelId::default(),
                sequence: Sequence::default(),
            }),
        );
    }

    #[test]
    fn commitments_path_parses() {
        let path = "commitments/ports/defaultPort/channels/channel-0/sequences/0";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(
            path.unwrap(),
            Path::Commitments {
                port_id: PortId::default(),
                channel_id: ChannelId::default(),
                sequence: Sequence::default(),
            },
        );
    }

    #[test]
    fn test_parse_acks_fn() {
        let path = "acks/ports/defaultPort/channels/channel-0/sequences/0";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_acks(&components),
            Some(Path::Acks {
                port_id: PortId::default(),
                channel_id: ChannelId::default(),
                sequence: Sequence::default(),
            }),
        );
    }

    #[test]
    fn acks_path_parses() {
        let path = "acks/ports/defaultPort/channels/channel-0/sequences/0";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(
            path.unwrap(),
            Path::Acks {
                port_id: PortId::default(),
                channel_id: ChannelId::default(),
                sequence: Sequence::default(),
            },
        );
    }

    #[test]
    fn test_parse_receipts_fn() {
        let path = "receipts/ports/defaultPort/channels/channel-0/sequences/0";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_receipts(&components),
            Some(Path::Receipts {
                port_id: PortId::default(),
                channel_id: ChannelId::default(),
                sequence: Sequence::default(),
            }),
        );
    }

    #[test]
    fn receipts_path_parses() {
        let path = "receipts/ports/defaultPort/channels/channel-0/sequences/0";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(
            path.unwrap(),
            Path::Receipts {
                port_id: PortId::default(),
                channel_id: ChannelId::default(),
                sequence: Sequence::default(),
            },
        );
    }

    #[test]
    fn test_parse_upgrades_fn() {
        let path = "upgradedIBCState/0/upgradedClient";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_upgrades(&components),
            Some(Path::Upgrade(ClientUpgradePath::UpgradedClientState(0))),
        );

        let path = "upgradedIBCState/0/upgradedConsState";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_upgrades(&components),
            Some(Path::Upgrade(
                ClientUpgradePath::UpgradedClientConsensusState(0)
            )),
        )
    }

    #[test]
    fn upgrade_client_state_path_parses() {
        let path = "upgradedIBCState/0/upgradedClient";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(
            path.unwrap(),
            Path::Upgrade(ClientUpgradePath::UpgradedClientState(0)),
        );
    }

    #[test]
    fn upgrade_client_consensus_state_path_parses() {
        let path = "upgradedIBCState/0/upgradedConsState";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(
            path.unwrap(),
            Path::Upgrade(ClientUpgradePath::UpgradedClientConsensusState(0)),
        );
    }
}
