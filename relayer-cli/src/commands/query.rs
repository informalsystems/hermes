//! `query` subcommand

use abscissa_core::{Command, Options, Runnable};

use crate::commands::query::channels::QueryChannelsCmd;
use crate::commands::query::trace::QueryTraceCmd;

mod channel;
mod channels;
mod client;
mod clients;
mod connection;
mod connections;
mod packet;
mod trace;
mod tx;

/// `query` subcommand
#[derive(Command, Debug, Options, Runnable)]
pub enum QueryCmd {
    /// The `query client` subcommand
    #[options(help = "Query information about clients")]
    Client(QueryClientCmds),

    #[options(help = "Query the identifiers of all clients on a chain")]
    Clients(clients::QueryAllClientsCmd),

    /// The `query connection` subcommand
    #[options(help = "Query information about connections")]
    Connection(QueryConnectionCmds),

    /// The `query connections` subcommand
    #[options(help = "Query the identifiers of all connections on a chain")]
    Connections(connections::QueryConnectionsCmd),

    /// The `query channel` subcommand
    #[options(help = "Query information about channels")]
    Channel(QueryChannelCmds),

    /// The `query channels` subcommand
    #[options(help = "Query the identifiers of all channels on a given chain")]
    Channels(QueryChannelsCmd),

    /// The `query trace` subcommand
    #[options(help = "Query the trace of channels on a given chain")]
    Trace(QueryTraceCmd),

    /// The `query packet` subcommand
    #[options(help = "Query information about packets")]
    Packet(QueryPacketCmds),

    /// The `query tx` subcommand
    #[options(help = "Query information about transactions")]
    Tx(tx::QueryTxCmd),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum QueryClientCmds {
    /// The `query client state` subcommand
    #[options(help = "Query the client full state")]
    State(client::QueryClientStateCmd),

    /// The `query client consensus` subcommand
    #[options(help = "Query the client consensus state")]
    Consensus(client::QueryClientConsensusCmd),

    /// The `query client header` subcommand
    #[options(help = "Query for the header used in a client update at a certain height")]
    Header(client::QueryClientHeaderCmd),

    /// The `query client connections` subcommand
    #[options(help = "Query the client connections")]
    Connections(client::QueryClientConnectionsCmd),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum QueryConnectionCmds {
    /// The `query connection end` subcommand
    #[options(help = "Query connection end")]
    End(connection::QueryConnectionEndCmd),

    /// The `query connection channels` subcommand
    #[options(help = "Query connection channels")]
    Channels(connection::QueryConnectionChannelsCmd),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum QueryChannelCmds {
    /// The `query channel end` subcommand
    #[options(help = "Query channel end")]
    End(channel::QueryChannelEndCmd),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum QueryPacketCmds {
    /// The `query packet commitments` subcommand
    #[options(help = "Query packet commitments")]
    Commitments(packet::QueryPacketCommitmentsCmd),

    /// The `query packet commitment` subcommand
    #[options(help = "Query packet commitment")]
    Commitment(packet::QueryPacketCommitmentCmd),

    /// The `query packet acks` subcommand
    #[options(help = "Query packet acknowledgments")]
    Acks(packet::QueryPacketAcknowledgementsCmd),

    /// The `query packet ack` subcommand
    #[options(help = "Query packet acknowledgment")]
    Ack(packet::QueryPacketAcknowledgmentCmd),

    /// The `query packet unreceived-packets` subcommand
    #[options(help = "Query unreceived packets")]
    UnreceivedPackets(packet::QueryUnreceivedPacketsCmd),

    /// The `query packet unreceived-acks` subcommand
    #[options(help = "Query unreceived acknowledgments")]
    UnreceivedAcks(packet::QueryUnreceivedAcknowledgementCmd),
}
