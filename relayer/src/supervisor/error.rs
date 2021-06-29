use flex_error::define_error;

use ibc::ics03_connection::connection::Counterparty;
use ibc::ics24_host::identifier::{ChainId, ChannelId, ConnectionId};

use crate::error::Error as RelayerError;

define_error! {
    Error {
        ChannelUninitialized
            {
                channel_id: ChannelId,
                chain_id: ChainId,
            }
            |e| {
                format!("channel {0} on chain {1} is not open",
                    e.channel_id, e.chain_id)
            },

        ChannelConnectionUninitialized
            {
                channel_id: ChannelId,
                chain_id: ChainId,
                counterparty: Counterparty
            }
            |e| {
                format!("channel {} on chain {} has a connection with uninitialized counterparty {:?}",
                    e.channel_id, e.chain_id, e.counterparty)
            },

        ConnectionNotOpen
            {
                connection_id: ConnectionId,
                channel_id: ChannelId,
                chain_id: ChainId,
            }
            |e| {
                format!("connection {0} (underlying channel {1}) on chain {2} is not open",
                    e.connection_id, e.channel_id, e.chain_id)
            },

        MissingConnectionHops
            {
                channel_id: ChannelId,
                chain_id: ChainId,
            }
            |e| {
                format!("channel {0} on chain {1} has no connection hops specified",
                    e.channel_id, e.chain_id)
            },

        Relayer
            [ RelayerError ]
            |_| { "relayer error" },

    }
}
