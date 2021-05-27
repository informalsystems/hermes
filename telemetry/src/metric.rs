use std::fmt;

use ibc::ics24_host::identifier::{ChainId, ChannelId, ClientId, PortId};

#[derive(Debug)]
pub enum MetricUpdate {
    Worker(WorkerType, Op),
    IbcClientMisbehaviour(ChainId, ClientId),
    IbcClientUpdate(ChainId, ClientId),
    IbcReceivePacket(ChainId, ChannelId, PortId, u64),
}

#[derive(Copy, Clone, Debug)]
pub enum WorkerType {
    Client,
    Channel,
    Packet,
}

impl fmt::Display for WorkerType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Client => write!(f, "client"),
            Self::Channel => write!(f, "channel"),
            Self::Packet => write!(f, "packet"),
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub enum Op {
    Add(i64),
    Sub(i64),
}

impl Op {
    pub fn to_i64(&self) -> i64 {
        match self {
            Self::Add(n) => *n,
            Self::Sub(n) => -n,
        }
    }
}
