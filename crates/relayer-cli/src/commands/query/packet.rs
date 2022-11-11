use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

mod ack;
mod acks;
mod commitment;
mod commitments;
mod pending;
mod pending_acks;
mod pending_sends;
mod util;

#[derive(Command, Debug, Parser, Runnable)]
pub enum QueryPacketCmds {
    /// Query packet commitments
    Commitments(commitments::QueryPacketCommitmentsCmd),

    /// Query packet commitment
    Commitment(commitment::QueryPacketCommitmentCmd),

    /// Query packet acknowledgments
    Acks(acks::QueryPacketAcknowledgementsCmd),

    /// Query packet acknowledgment
    Ack(ack::QueryPacketAcknowledgmentCmd),

    /// Query pending send packets
    PendingSends(pending_sends::QueryPendingSendsCmd),

    /// Query pending acknowledgments
    PendingAcks(pending_acks::QueryPendingAcksCmd),

    /// Output a summary of pending packets in both directions
    Pending(pending::QueryPendingPacketsCmd),
}
