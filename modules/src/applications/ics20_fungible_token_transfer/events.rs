use crate::applications::ics20_fungible_token_transfer::acknowledgement::Acknowledgement;
use crate::applications::ics20_fungible_token_transfer::address::Address;
use crate::applications::ics20_fungible_token_transfer::{Amount, DenomTrace, HashedDenom};

#[allow(unused)]
pub enum Event {
    Recv(RecvEvent),
    Ack(AckEvent),
    Timeout(TimeoutEvent),
    DenomTrace(DenomTraceEvent),
}

pub struct RecvEvent {
    pub receiver: Address,
    pub denom: DenomTrace,
    pub amount: Amount,
    pub ack_success: bool,
}

pub struct AckEvent {
    pub receiver: Address,
    pub denom: DenomTrace,
    pub amount: Amount,
    pub ack: Acknowledgement,
}

pub struct TimeoutEvent {
    pub refund_receiver: Address,
    pub refund_denom: DenomTrace,
    pub refund_amount: Amount,
}

pub struct DenomTraceEvent {
    pub trace_hash: HashedDenom,
    pub denom: DenomTrace,
}
