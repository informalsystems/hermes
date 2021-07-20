use flex_error::define_error;
use ibc::ics04_channel::channel::IdentifiedChannelEnd;
use ibc::ics24_host::identifier::ChainId;
use ibc_relayer::channel::ChannelError;
use ibc_relayer::connection::ConnectionError;
use ibc_relayer::error::Error as RelayerError;
use ibc_relayer::foreign_client::ForeignClientError;
use ibc_relayer::link::error::LinkError;
use ibc_relayer::supervisor::Error as SupervisorError;
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

        MissingCounterpartyChannelId
            { channel_end: IdentifiedChannelEnd }
            | e | {
                format_args!("the channel {:?} counterparty has no channel id",
                    e.channel_end)
            },

        Relayer
            [ RelayerError ]
            |_| { "relayer error" },

        Connection
            [ ConnectionError ]
            |_| { "connection error" },

        Packet
            [ PacketError ]
            |_| { "packet error" },

        Channel
            [ ChannelError ]
            |_| { "channel error" },

        ForeignClient
            [ ForeignClientError ]
            |_| { "foreign client error" },

        Supervisor
            [ SupervisorError ]
            |_| { "supervisor error" },

        Link
            [ LinkError ]
            |_| { "link error" },

        UpgradeChain
            [ UpgradeChainError ]
            |_| { "upgrade chain error" },
    }
}
