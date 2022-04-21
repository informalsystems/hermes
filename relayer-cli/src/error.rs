use flex_error::define_error;
use ibc::core::ics04_channel::channel::IdentifiedChannelEnd;
use ibc::core::ics24_host::identifier::ChainId;
use ibc_relayer::channel::ChannelError;
use ibc_relayer::connection::ConnectionError;
use ibc_relayer::error::Error as RelayerError;
use ibc_relayer::foreign_client::ForeignClientError;
use ibc_relayer::link::error::LinkError;
use ibc_relayer::supervisor::Error as SupervisorError;
use ibc_relayer::transfer::TransferError;
use ibc_relayer::upgrade_chain::UpgradeChainError;
use tendermint::Error as TendermintError;

define_error! {
    /// An error raised within the relayer CLI
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

        InvalidHash
            { hash: String }
            [ TendermintError ]
            | e | {
                format_args!("CLI argument error: could not parse '{}' into a valid hash",
                    e.hash)
            },

        CliArg
            { reason: String }
            | e | {
                format_args!("CLI argument error: {0}",
                    e.reason)
            },

        Keys
            |_| { "keys error" },

        MissingChainConfig
            { chain_id: ChainId }
            | e | {
                format_args!("missing chain with id '{}' in configuration file",
                    e.chain_id)
            },

        MissingCounterpartyChannelId
            { channel_end: IdentifiedChannelEnd }
            | e | {
                format_args!("this channel's counterparty has no channel id: {:?}",
                    e.channel_end)
            },

        Relayer
            [ RelayerError ]
            |_| { "relayer error" },

        Connection
            [ ConnectionError ]
            |_| { "connection error" },

        Transfer
            [ TransferError ]
            |_| { "transfer error" },

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
