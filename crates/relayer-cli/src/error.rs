//! All errors which can be raised from a command.

use std::io::Error as IoError;

use flex_error::{
    define_error,
    DisplayError,
};
use ibc_relayer::{
    channel::ChannelError,
    connection::ConnectionError,
    error::Error as RelayerError,
    foreign_client::ForeignClientError,
    keyring::errors::Error as KeyRingError,
    link::error::LinkError,
    spawn::SpawnError,
    supervisor::Error as SupervisorError,
    transfer::TransferError,
    upgrade_chain::UpgradeChainError,
};
use ibc_relayer_types::{
    applications::ics29_fee::error::Error as FeeError,
    core::{
        ics04_channel::channel::IdentifiedChannelEnd,
        ics24_host::identifier::ChainId,
    },
    signer::SignerError,
};
use tendermint::Error as TendermintError;

define_error! {
    /// An error raised within the relayer CLI
    Error {
        Config
            |_| { "config error" },

        Io
            [ DisplayError<IoError> ]
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
                format_args!("missing chain '{}' in configuration file",
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

        Spawn
            [ SpawnError ]
            |_| { "failed to spawn chain runtime" },

        Connection
            [ ConnectionError ]
            |_| { "connection error" },

        Fee
            [ FeeError ]
            |_| { "fee error" },

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

        Signer
            [ SignerError ]
            |_| { "signer error" },

        KeyRing
            [ KeyRingError ]
            |_| { "keyring error" },
    }
}
