use crate::applications::ics20_fungible_token_transfer::acknowledgement::Acknowledgement;
use crate::applications::ics20_fungible_token_transfer::address::Address;
use crate::applications::ics20_fungible_token_transfer::{
    Amount, DenomTrace, HashedDenom, MODULE_ID_STR,
};
use crate::events::ModuleEvent;
use crate::prelude::*;

const EVENT_TYPE_PACKET: &str = "fungible_token_packet";
const EVENT_TYPE_TIMEOUT: &str = "timeout";
const EVENT_TYPE_DENOM_TRACE: &str = "denomination_trace";
const EVENT_TYPE_TRANSFER: &str = "ibc_transfer";

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
    pub success: bool,
}

impl From<RecvEvent> for ModuleEvent {
    fn from(ev: RecvEvent) -> Self {
        let RecvEvent {
            receiver,
            denom,
            amount,
            success,
        } = ev;
        Self {
            kind: EVENT_TYPE_PACKET.to_string(),
            module_name: MODULE_ID_STR.parse().expect("invalid ModuleId"),
            attributes: vec![
                ("receiver", receiver).into(),
                ("denom", denom).into(),
                ("amount", amount).into(),
                ("success", success).into(),
            ],
        }
    }
}

pub struct AckEvent {
    pub receiver: Address,
    pub denom: DenomTrace,
    pub amount: Amount,
    pub acknowledgement: Acknowledgement,
}

impl From<AckEvent> for ModuleEvent {
    fn from(ev: AckEvent) -> Self {
        let AckEvent {
            receiver,
            denom,
            amount,
            acknowledgement,
        } = ev;
        Self {
            kind: EVENT_TYPE_PACKET.to_string(),
            module_name: MODULE_ID_STR.parse().expect("invalid ModuleId"),
            attributes: vec![
                ("receiver", receiver).into(),
                ("denom", denom).into(),
                ("amount", amount).into(),
                ("acknowledgement", acknowledgement).into(),
            ],
        }
    }
}

pub struct TimeoutEvent {
    pub refund_receiver: Address,
    pub refund_denom: DenomTrace,
    pub refund_amount: Amount,
}

impl From<TimeoutEvent> for ModuleEvent {
    fn from(ev: TimeoutEvent) -> Self {
        let TimeoutEvent {
            refund_receiver,
            refund_denom,
            refund_amount,
        } = ev;
        Self {
            kind: EVENT_TYPE_TIMEOUT.to_string(),
            module_name: MODULE_ID_STR.parse().expect("invalid ModuleId"),
            attributes: vec![
                ("refund_receiver", refund_receiver).into(),
                ("refund_denom", refund_denom).into(),
                ("refund_amount", refund_amount).into(),
            ],
        }
    }
}

pub struct DenomTraceEvent {
    pub trace_hash: HashedDenom,
    pub denom: DenomTrace,
}

impl From<DenomTraceEvent> for ModuleEvent {
    fn from(ev: DenomTraceEvent) -> Self {
        let DenomTraceEvent { trace_hash, denom } = ev;
        Self {
            kind: EVENT_TYPE_DENOM_TRACE.to_string(),
            module_name: MODULE_ID_STR.parse().expect("invalid ModuleId"),
            attributes: vec![("trace_hash", trace_hash).into(), ("denom", denom).into()],
        }
    }
}

impl From<Event> for ModuleEvent {
    fn from(ev: Event) -> Self {
        match ev {
            Event::Recv(ev) => ev.into(),
            Event::Ack(ev) => ev.into(),
            Event::Timeout(ev) => ev.into(),
            Event::DenomTrace(ev) => ev.into(),
            Event::Transfer(ev) => ev.into(),
        }
    }
}
