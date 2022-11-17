//! Error type used for the tests.

use core::convert::{From, Into};
use eyre::Report;
use flex_error::{define_error, TraceError};
use ibc_relayer::connection::ConnectionError;
use ibc_relayer::error::Error as RelayerError;
use ibc_relayer::link::error::LinkError;
use ibc_relayer::supervisor::error::Error as SupervisorError;
use ibc_relayer::transfer::TransferError;
use ibc_relayer::{channel::error::ChannelError, upgrade_chain::UpgradeChainError};
use std::io::{Error as IoError, ErrorKind as IoErrorKind};

define_error! {
    Error {
        Generic
            [ TraceError<Report> ]
            | _ | { "generic error" },

        Assertion
            { message: String }
            | e | { format_args!("assertion failure: {}", e.message) },

        Io
            [ TraceError<IoError> ]
            | _ | { "io error"},

        CommandNotFound
            { command: String }
            [ TraceError<IoError> ]
            | e | { format_args!("failed to execute command: {}. make sure it is available in $PATH", e.command) },

        Relayer
            [ RelayerError ]
            | _ | { "relayer error"},

        Supervisor
            [ SupervisorError ]
            | _ | { "supervisor error"},

        Channel
            [ ChannelError ]
            | _ | { "channel error"},

        Connection
            [ ConnectionError ]
            | _ | { "connection error"},

        Transfer
            [ TransferError ]
            | _ | { "transfer error"},

        Link
            [ LinkError ]
            | _ | { "link error" },

        Retry
            {
                task_name: String,
                attempts: u16,
            }
            | e | {
                format_args!(
                    "Expected task to eventually succeeed, but failed after {} attempts: {}",
                    e.attempts,
                    e.task_name
                )
            },

        UpgradeChain
            [ UpgradeChainError ]
            | _ | { "upgrade chain error" },

        QueryClient
            | _ | { "error querying client" },

        IncorrectProposal
            | _ | { "error decoding the Proposal to an UpgradeProposal" },

        IncorrectProposalTypeUrl
            { type_url: String }
            | e | format_args!("expected /ibc.core.client.v1.UpgradeProposal but got {}", e.type_url),

        EmptyProposal
            | _ | { "the Proposal content is empty" },

        EmptyPlan
            | _ | { "The plan in the UpgradeProposal is empty" },
    }
}

pub fn handle_generic_error(e: impl Into<Report>) -> Error {
    Error::generic(e.into())
}

pub fn handle_exec_error(command: &str) -> impl FnOnce(IoError) -> Error + '_ {
    |e| match e.kind() {
        IoErrorKind::NotFound => Error::command_not_found(command.to_string(), e),
        _ => Error::io(e),
    }
}

impl From<Report> for Error {
    fn from(e: Report) -> Self {
        Error::generic(e)
    }
}

impl From<IoError> for Error {
    fn from(e: IoError) -> Self {
        Error::io(e)
    }
}

impl From<RelayerError> for Error {
    fn from(e: RelayerError) -> Self {
        Error::relayer(e)
    }
}

impl From<SupervisorError> for Error {
    fn from(e: SupervisorError) -> Self {
        Error::supervisor(e)
    }
}

impl From<ChannelError> for Error {
    fn from(e: ChannelError) -> Self {
        Error::channel(e)
    }
}

impl From<ConnectionError> for Error {
    fn from(e: ConnectionError) -> Self {
        Error::connection(e)
    }
}

impl From<TransferError> for Error {
    fn from(e: TransferError) -> Self {
        Error::transfer(e)
    }
}

impl From<LinkError> for Error {
    fn from(e: LinkError) -> Self {
        Error::link(e)
    }
}
