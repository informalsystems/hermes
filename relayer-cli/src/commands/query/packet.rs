use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};

mod ack;
mod acks;
mod commitment;
mod commitments;
mod pending;
mod unreceived_acks;
mod unreceived_packets;

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

    /// Query unreceived packets
    UnreceivedPackets(unreceived_packets::QueryUnreceivedPacketsCmd),

    /// Query unreceived acknowledgments
    UnreceivedAcks(unreceived_acks::QueryUnreceivedAcknowledgementCmd),

    /// Output a summary of pending packets in both directions
    Pending(pending::QueryPendingPacketsCmd),
}
