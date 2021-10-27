use flex_error::define_error;

use ibc::core::ics03_connection::connection::Counterparty;
use ibc::core::ics24_host::identifier::{ChainId, ChannelId, ConnectionId, PortId};

use crate::error::Error as RelayerError;
use crate::registry::SpawnError;
use crate::worker::WorkerError;

define_error! {
    Error {
        ChannelUninitialized
            {
                port_id: PortId,
                channel_id: ChannelId,
                chain_id: ChainId,
            }
            |e| {
                format_args!("channel {0} on chain {1} is not open",
                    e.channel_id, e.chain_id)
            },

        ChannelConnectionUninitialized
            {
                channel_id: ChannelId,
                chain_id: ChainId,
                counterparty: Counterparty
            }
            |e| {
                format_args!("channel {} on chain {} has a connection with uninitialized counterparty {:?}",
                    e.channel_id, e.chain_id, e.counterparty)
            },

        ConnectionNotOpen
            {
                connection_id: ConnectionId,
                channel_id: ChannelId,
                chain_id: ChainId,
            }
            |e| {
                format_args!("connection {0} (underlying channel {1}) on chain {2} is not open",
                    e.connection_id, e.channel_id, e.chain_id)
            },

        MissingConnectionHops
            {
                channel_id: ChannelId,
                chain_id: ChainId,
            }
            |e| {
                format_args!("channel {0} on chain {1} has no connection hops specified",
                    e.channel_id, e.chain_id)
            },

        MissingCounterpartyChannelId
            |_| { "failed due to missing counterparty channel id" },

        Relayer
            [ RelayerError ]
            |_| { "relayer error" },

        NoChainsAvailable
            |_| { "supervisor was not able to connect to any chains" },

        Spawn
            [ SpawnError ]
            |_| { "supervisor was not able to connect to any chains" },

        Worker
            [ WorkerError ]
            |_| { "worker error" },
    }
}
