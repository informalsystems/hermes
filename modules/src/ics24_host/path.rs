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

impl FromStr for Path {
    type Err = PathError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let components: Vec<&str> = s.split('/').collect();

        parse_client_paths(&components)
            // .or_else(|| parse_connections(&components))
            // .or_else(|| parse_ports(&components))
            // .or_else(|| parse_channel_ends(&components))
            // .or_else(|| parse_seq_sends(&components))
            // .or_else(|| parse_seq_recvs(&components))
            // .or_else(|| parse_seq_acks(&components))
            // .or_else(|| parse_commitments(&components))
            // .or_else(|| parse_acks(&components))
            // .or_else(|| parse_receipts(&components))
            // .or_else(|| parse_upgrades(&components))
            .ok_or_else(|| PathError::parse_failure(s.to_string()))
    }
}

fn parse_client_paths(components: &[&str]) -> Option<Path> {
    if "clients" != *components.first().unwrap() {
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

        let epoch_height: Vec<&str> = components.last().unwrap().split('-').collect();

        if epoch_height.len() != 2 {
            return None;
        }

        let epoch = epoch_height.first().unwrap().parse::<u64>();
        let height = epoch_height.last().unwrap().parse::<u64>();

        if epoch.is_err() || height.is_err() {
            return None;
        }

        Some(Path::ClientConsensusState {
            client_id,
            epoch: epoch.unwrap(),
            height: height.unwrap(),
        })
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::str::FromStr;

    #[test]
    fn parse_fromstr_errors() {
        let path = Path::from_str("clients/clientType");

        assert!(path.is_err());
    }

    #[test]
    fn parse_client_type_works() {
        let path = "clients/07-tendermint-0/clientType";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_client_type(&components),
            Some(Path::ClientType(ClientId::default()))
        );
    }

    #[test]
    fn parse_client_state_works() {
        let path = "clients/07-tendermint-0/clientState";
        let components: Vec<&str> = path.split('/').collect();

        assert_eq!(
            parse_client_state(&components),
            Some(Path::ClientState(ClientId::default()))
        );
    }
}
