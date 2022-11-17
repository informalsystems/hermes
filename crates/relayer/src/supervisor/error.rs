use flex_error::define_error;

use ibc_relayer_types::core::ics03_connection::connection::Counterparty;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ChannelId, ConnectionId, PortId};

use crate::error::Error as RelayerError;
use crate::spawn::SpawnError;
use crate::supervisor::scan::Error as ScanError;

define_error! {
    Error {
        ChannelUninitialized
            {
                port_id: PortId,
                channel_id: ChannelId,
                chain_id: ChainId,
            }
            |e| {
                format_args!("channel {0}/{1} on chain {2} is not open",
                    e.port_id, e.channel_id, e.chain_id)
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
            |_| { "supervisor was not able to spawn chain runtime" },

        Scan
            [ ScanError ]
            |_| { "supervisor encountered an error when scanning chains" },

        HandleSend
            |_| { "failed to send a command to the supervisor through a channel" },

        HandleRecv
            |_| { "failed to receive the result of a command from the supervisor through a channel" },
    }
}

impl Error {
    pub fn log_as_debug(&self) -> bool {
        matches!(self.detail(), ErrorDetail::Spawn(e) if e.source.log_as_debug())
    }
}
