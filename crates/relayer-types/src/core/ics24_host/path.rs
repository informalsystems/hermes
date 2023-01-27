use crate::prelude::*;

/// Path-space as listed in ICS-024
/// https://github.com/cosmos/ibc/tree/master/spec/core/ics-024-host-requirements#path-space
/// Some of these are implemented in other ICSs, but ICS-024 has a nice summary table.
///
use core::str::FromStr;

use crate::core::ics04_channel::packet::Sequence;
use crate::core::ics24_host::identifier::{ChannelId, ClientId, ConnectionId, PortId};

use derive_more::{Display, From};
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
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, From, Display)]
pub enum Path {
    ClientType(ClientTypePath),
    ClientState(ClientStatePath),
    ClientConsensusState(ClientConsensusStatePath),
    ClientConnections(ClientConnectionsPath),
    Connections(ConnectionsPath),
    Ports(PortsPath),
    ChannelEnds(ChannelEndsPath),
    SeqSends(SeqSendsPath),
    SeqRecvs(SeqRecvsPath),
    SeqAcks(SeqAcksPath),
    Commitments(CommitmentsPath),
    Acks(AcksPath),
    Receipts(ReceiptsPath),
    Upgrade(ClientUpgradePath),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Display)]
#[display(fmt = "clients/{_0}/clientType")]
pub struct ClientTypePath(pub ClientId);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Display)]
#[display(fmt = "clients/{_0}/clientState")]
pub struct ClientStatePath(pub ClientId);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Display)]
#[display(fmt = "clients/{client_id}/consensusStates/{epoch}-{height}")]
pub struct ClientConsensusStatePath {
    pub client_id: ClientId,
    pub epoch: u64,
    pub height: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Display)]
#[display(fmt = "clients/{_0}/connections")]
pub struct ClientConnectionsPath(pub ClientId);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Display)]
#[display(fmt = "connections/{_0}")]
pub struct ConnectionsPath(pub ConnectionId);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Display)]
#[display(fmt = "ports/{_0}")]
pub struct PortsPath(pub PortId);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Display)]
#[display(fmt = "channelEnds/ports/{_0}/channels/{_1}")]
pub struct ChannelEndsPath(pub PortId, pub ChannelId);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Display)]
#[display(fmt = "nextSequenceSend/ports/{_0}/channels/{_1}")]
pub struct SeqSendsPath(pub PortId, pub ChannelId);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Display)]
#[display(fmt = "nextSequenceRecv/ports/{_0}/channels/{_1}")]
pub struct SeqRecvsPath(pub PortId, pub ChannelId);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Display)]
#[display(fmt = "nextSequenceAck/ports/{_0}/channels/{_1}")]
pub struct SeqAcksPath(pub PortId, pub ChannelId);

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Display)]
#[display(fmt = "commitments/ports/{port_id}/channels/{channel_id}/sequences/{sequence}")]
pub struct CommitmentsPath {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub sequence: Sequence,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Display)]
#[display(fmt = "acks/ports/{port_id}/channels/{channel_id}/sequences/{sequence}")]
pub struct AcksPath {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub sequence: Sequence,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Display)]
#[display(fmt = "receipts/ports/{port_id}/channels/{channel_id}/sequences/{sequence}")]
pub struct ReceiptsPath {
    pub port_id: PortId,
    pub channel_id: ChannelId,
    pub sequence: Sequence,
}

/// Paths that are specific for client upgrades.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Display)]
pub enum ClientUpgradePath {
    #[display(fmt = "{UPGRADED_IBC_STATE}/{_0}/{UPGRADED_CLIENT_STATE}")]
    UpgradedClientState(u64),
    #[display(fmt = "{UPGRADED_IBC_STATE}/{_0}/{UPGRADED_CLIENT_CONSENSUS_STATE}")]
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
            "clientType" => Some(ClientTypePath(client_id).into()),
            "clientState" => Some(ClientStatePath(client_id).into()),
            "connections" => Some(ClientConnectionsPath(client_id).into()),
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

        Some(
            ClientConsensusStatePath {
                client_id,
                epoch,
                height,
            }
            .into(),
        )
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

    Some(ConnectionsPath(connection_id).into())
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

    Some(PortsPath(port_id).into())
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

    let port_id = if let Some(Path::Ports(PortsPath(port_id))) = port {
        port_id
    } else {
        return None;
    };

    let channel_id = if let Some(SubPath::Channels(channel_id)) = channel {
        channel_id
    } else {
        return None;
    };

    Some(ChannelEndsPath(port_id, channel_id).into())
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

    let port_id = if let Some(Path::Ports(PortsPath(port_id))) = port {
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
        "nextSequenceSend" => Some(SeqSendsPath(port_id, channel_id).into()),
        "nextSequenceRecv" => Some(SeqRecvsPath(port_id, channel_id).into()),
        "nextSequenceAck" => Some(SeqAcksPath(port_id, channel_id).into()),
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

    let port_id = if let Some(Path::Ports(PortsPath(port_id))) = port {
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

    Some(
        CommitmentsPath {
            port_id,
            channel_id,
            sequence,
        }
        .into(),
    )
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

    let port_id = if let Some(Path::Ports(PortsPath(port_id))) = port {
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

    Some(
        AcksPath {
            port_id,
            channel_id,
            sequence,
        }
        .into(),
    )
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

    let port_id = if let Some(Path::Ports(PortsPath(port_id))) = port {
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

    Some(
        ReceiptsPath {
            port_id,
            channel_id,
            sequence,
        }
        .into(),
    )
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
        UPGRADED_CLIENT_STATE => Some(ClientUpgradePath::UpgradedClientState(height).into()),
        UPGRADED_CLIENT_CONSENSUS_STATE => {
            Some(ClientUpgradePath::UpgradedClientConsensusState(height).into())
        }
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
            Some(Path::ClientType(ClientTypePath(ClientId::default())))
        );

        let path = "clients/07-tendermint-0/clientState";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_client_paths(&components),
            Some(Path::ClientState(ClientStatePath(ClientId::default())))
        );

        let path = "clients/07-tendermint-0/consensusStates/15-31";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_client_paths(&components),
            Some(Path::ClientConsensusState(ClientConsensusStatePath {
                client_id: ClientId::default(),
                epoch: 15,
                height: 31,
            }))
        );
    }

    #[test]
    fn client_type_path_parses() {
        let path = "clients/07-tendermint-0/clientType";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(
            path.unwrap(),
            Path::ClientType(ClientTypePath(ClientId::default()))
        );
    }

    #[test]
    fn client_state_path_parses() {
        let path = "clients/07-tendermint-0/clientState";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(
            path.unwrap(),
            Path::ClientState(ClientStatePath(ClientId::default()))
        );
    }

    #[test]
    fn client_consensus_state_path_parses() {
        let path = "clients/07-tendermint-0/consensusStates/15-31";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(
            path.unwrap(),
            Path::ClientConsensusState(ClientConsensusStatePath {
                client_id: ClientId::default(),
                epoch: 15,
                height: 31,
            })
        );
    }

    #[test]
    fn client_connections_path_parses() {
        let path = "clients/07-tendermint-0/connections";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(
            path.unwrap(),
            Path::ClientConnections(ClientConnectionsPath(ClientId::default()))
        );
    }

    #[test]
    fn test_parse_connections_fn() {
        let path = "connections/connection-0";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_connections(&components),
            Some(Path::Connections(ConnectionsPath(ConnectionId::new(0)))),
        );
    }

    #[test]
    fn connections_path_parses() {
        let path = "connections/connection-0";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(
            path.unwrap(),
            Path::Connections(ConnectionsPath(ConnectionId::new(0)))
        );
    }

    #[test]
    fn test_parse_ports_fn() {
        let path = "ports/defaultPort";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_ports(&components),
            Some(Path::Ports(PortsPath(PortId::default()))),
        );
    }

    #[test]
    fn ports_path_parses() {
        let path = "ports/defaultPort";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(path.unwrap(), Path::Ports(PortsPath(PortId::default())));
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
            Some(Path::ChannelEnds(ChannelEndsPath(
                PortId::default(),
                ChannelId::default()
            ))),
        );
    }

    #[test]
    fn channel_ends_path_parses() {
        let path = "channelEnds/ports/defaultPort/channels/channel-0";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(
            path.unwrap(),
            Path::ChannelEnds(ChannelEndsPath(PortId::default(), ChannelId::default())),
        );
    }

    #[test]
    fn test_parse_seqs_fn() {
        let path = "nextSequenceSend/ports/defaultPort/channels/channel-0";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_seqs(&components),
            Some(Path::SeqSends(SeqSendsPath(
                PortId::default(),
                ChannelId::default()
            ))),
        );

        let path = "nextSequenceRecv/ports/defaultPort/channels/channel-0";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_seqs(&components),
            Some(Path::SeqRecvs(SeqRecvsPath(
                PortId::default(),
                ChannelId::default()
            ))),
        );

        let path = "nextSequenceAck/ports/defaultPort/channels/channel-0";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_seqs(&components),
            Some(Path::SeqAcks(SeqAcksPath(
                PortId::default(),
                ChannelId::default()
            ))),
        );
    }

    #[test]
    fn sequence_send_path_parses() {
        let path = "nextSequenceSend/ports/defaultPort/channels/channel-0";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(
            path.unwrap(),
            Path::SeqSends(SeqSendsPath(PortId::default(), ChannelId::default())),
        );
    }

    #[test]
    fn sequence_recv_path_parses() {
        let path = "nextSequenceRecv/ports/defaultPort/channels/channel-0";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(
            path.unwrap(),
            Path::SeqRecvs(SeqRecvsPath(PortId::default(), ChannelId::default())),
        );
    }

    #[test]
    fn sequence_ack_path_parses() {
        let path = "nextSequenceAck/ports/defaultPort/channels/channel-0";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(
            path.unwrap(),
            Path::SeqAcks(SeqAcksPath(PortId::default(), ChannelId::default())),
        );
    }

    #[test]
    fn test_parse_commitments_fn() {
        let path = "commitments/ports/defaultPort/channels/channel-0/sequences/0";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_commitments(&components),
            Some(Path::Commitments(CommitmentsPath {
                port_id: PortId::default(),
                channel_id: ChannelId::default(),
                sequence: Sequence::default(),
            })),
        );
    }

    #[test]
    fn commitments_path_parses() {
        let path = "commitments/ports/defaultPort/channels/channel-0/sequences/0";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(
            path.unwrap(),
            Path::Commitments(CommitmentsPath {
                port_id: PortId::default(),
                channel_id: ChannelId::default(),
                sequence: Sequence::default(),
            }),
        );
    }

    #[test]
    fn test_parse_acks_fn() {
        let path = "acks/ports/defaultPort/channels/channel-0/sequences/0";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_acks(&components),
            Some(Path::Acks(AcksPath {
                port_id: PortId::default(),
                channel_id: ChannelId::default(),
                sequence: Sequence::default(),
            })),
        );
    }

    #[test]
    fn acks_path_parses() {
        let path = "acks/ports/defaultPort/channels/channel-0/sequences/0";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(
            path.unwrap(),
            Path::Acks(AcksPath {
                port_id: PortId::default(),
                channel_id: ChannelId::default(),
                sequence: Sequence::default(),
            }),
        );
    }

    #[test]
    fn test_parse_receipts_fn() {
        let path = "receipts/ports/defaultPort/channels/channel-0/sequences/0";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_receipts(&components),
            Some(Path::Receipts(ReceiptsPath {
                port_id: PortId::default(),
                channel_id: ChannelId::default(),
                sequence: Sequence::default(),
            })),
        );
    }

    #[test]
    fn receipts_path_parses() {
        let path = "receipts/ports/defaultPort/channels/channel-0/sequences/0";
        let path = Path::from_str(path);

        assert!(path.is_ok());
        assert_eq!(
            path.unwrap(),
            Path::Receipts(ReceiptsPath {
                port_id: PortId::default(),
                channel_id: ChannelId::default(),
                sequence: Sequence::default(),
            }),
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
