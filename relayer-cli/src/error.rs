use flex_error::{define_error, DisplayOnly};
use ibc::ics24_host::identifier::ChainId;
use ibc_relayer::channel::ChannelError;
use ibc_relayer::connection::ConnectionError;
use ibc_relayer::error::Error as RelayerError;
use ibc_relayer::foreign_client::ForeignClientError;
use ibc_relayer::link::LinkError;
use ibc_relayer::transfer::PacketError;
use ibc_relayer::upgrade_chain::UpgradeChainError;

define_error! {
    Error {
        Config
            |_| { "config error" },

        Io
            |_| { "I/O error" },

        Query
            |_| { "query error" },

        Runtime
            |_| { "chain runtime error" },

        Tx
            |_| { "tx error" },

        Keys
            |_| { "keys error" },

        MissingConfig
            { chain_id: ChainId }
            | e | {
                format_args!("missing chain for id ({}) in configuration file",
                    e.chain_id)
            },

        Relayer
            [ RelayerError ]
            |_| { "relayer error" },

        Connection
            [ DisplayOnly<ConnectionError> ]
            |_| { "connection error" },

        Packet
            [ DisplayOnly<PacketError> ]
            |_| { "packet error" },

        Channel
            [ ChannelError ]
            |_| { "channel error" },

        ForeignClient
            [ DisplayOnly<ForeignClientError> ]
            |_| { "foreign client error" },

        Link
            [ DisplayOnly<LinkError> ]
            |_| { "link error" },

        UpgradeChain
            [ DisplayOnly<UpgradeChainError> ]
            |_| { "upgrade chain error" },
    }
}
