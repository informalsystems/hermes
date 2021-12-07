//! `query` subcommand

use abscissa_core::{Clap, Command, Runnable};

use crate::commands::query::channel_ends::QueryChannelEndsCmd;
use crate::commands::query::channels::QueryChannelsCmd;
use crate::commands::query::packet::QueryPacketCmds;

mod channel;
mod channel_ends;
mod channels;
mod client;
mod clients;
mod connection;
mod connections;
mod packet;
mod tx;

/// `query` subcommand
#[derive(Command, Debug, Clap, Runnable)]
pub enum QueryCmd {
    /// The `query client` subcommand
    #[clap(subcommand, about = "Query information about clients")]
    Client(QueryClientCmds),

    #[clap(about = "Query the identifiers of all clients on a chain")]
    Clients(clients::QueryAllClientsCmd),

    /// The `query connection` subcommand
    #[clap(subcommand, about = "Query information about connections")]
    Connection(QueryConnectionCmds),

    /// The `query connections` subcommand
    #[clap(about = "Query the identifiers of all connections on a chain")]
    Connections(connections::QueryConnectionsCmd),

    /// The `query channel` subcommand
    #[clap(subcommand, about = "Query information about channels")]
    Channel(QueryChannelCmds),

    /// The `query channels` subcommand
    #[clap(about = "Query the identifiers of all channels on a given chain")]
    Channels(QueryChannelsCmd),

    /// The `query packet` subcommand
    #[clap(subcommand, about = "Query information about packets")]
    Packet(QueryPacketCmds),

    /// The `query tx` subcommand
    #[clap(subcommand, about = "Query information about transactions")]
    Tx(tx::QueryTxCmd),
}

#[derive(Command, Debug, Clap, Runnable)]
pub enum QueryClientCmds {
    /// The `query client state` subcommand
    #[clap(about = "Query the client full state")]
    State(client::QueryClientStateCmd),

    /// The `query client consensus` subcommand
    #[clap(about = "Query the client consensus state")]
    Consensus(client::QueryClientConsensusCmd),

    /// The `query client header` subcommand
    #[clap(about = "Query for the header used in a client update at a certain height")]
    Header(client::QueryClientHeaderCmd),

    /// The `query client connections` subcommand
    #[clap(about = "Query the client connections")]
    Connections(client::QueryClientConnectionsCmd),
}

#[derive(Command, Debug, Clap, Runnable)]
pub enum QueryConnectionCmds {
    /// The `query connection end` subcommand
    #[clap(about = "Query connection end")]
    End(connection::QueryConnectionEndCmd),

    /// The `query connection channels` subcommand
    #[clap(about = "Query connection channels")]
    Channels(connection::QueryConnectionChannelsCmd),
}

#[derive(Command, Debug, Clap, Runnable)]
pub enum QueryChannelCmds {
    /// The `query channel end` subcommand
    #[clap(about = "Query channel end")]
    End(channel::QueryChannelEndCmd),

    /// The `query channel ends` subcommand
    #[clap(about = "Query channel ends and underlying connection and client objects")]
    Ends(QueryChannelEndsCmd),
}
