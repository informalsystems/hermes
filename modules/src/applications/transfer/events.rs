use crate::applications::transfer::acknowledgement::Acknowledgement;
use crate::applications::transfer::{Amount, PrefixedDenom, MODULE_ID_STR};
use crate::events::ModuleEvent;
use crate::prelude::*;
use crate::signer::Signer;

const EVENT_TYPE_PACKET: &str = "fungible_token_packet";
const EVENT_TYPE_TIMEOUT: &str = "timeout";
const EVENT_TYPE_DENOM_TRACE: &str = "denomination_trace";
const EVENT_TYPE_TRANSFER: &str = "ibc_transfer";

pub enum Event {
    Recv(RecvEvent),
    Ack(AckEvent),
    AckStatus(AckStatusEvent),
    Timeout(TimeoutEvent),
    DenomTrace(DenomTraceEvent),
    Transfer(TransferEvent),
}

pub struct RecvEvent {
    pub receiver: Signer,
    pub denom: PrefixedDenom,
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
    pub receiver: Signer,
    pub denom: PrefixedDenom,
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

pub struct AckStatusEvent {
    pub acknowledgement: Acknowledgement,
}

impl From<AckStatusEvent> for ModuleEvent {
    fn from(ev: AckStatusEvent) -> Self {
        let AckStatusEvent { acknowledgement } = ev;
        let mut event = Self {
            kind: EVENT_TYPE_PACKET.to_string(),
            module_name: MODULE_ID_STR.parse().expect("invalid ModuleId"),
            attributes: vec![],
        };
        let attr_label = match acknowledgement {
            Acknowledgement::Success(_) => "success",
            Acknowledgement::Error(_) => "error",
        };
        event
            .attributes
            .push((attr_label, acknowledgement.to_string()).into());
        event
    }
}

pub struct TimeoutEvent {
    pub refund_receiver: Signer,
    pub refund_denom: PrefixedDenom,
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
    pub trace_hash: Option<String>,
    pub denom: PrefixedDenom,
}

impl From<DenomTraceEvent> for ModuleEvent {
    fn from(ev: DenomTraceEvent) -> Self {
        let DenomTraceEvent { trace_hash, denom } = ev;
        let mut ev = Self {
            kind: EVENT_TYPE_DENOM_TRACE.to_string(),
            module_name: MODULE_ID_STR.parse().expect("invalid ModuleId"),
            attributes: vec![("denom", denom).into()],
        };
        if let Some(hash) = trace_hash {
            ev.attributes.push(("trace_hash", hash).into());
        }
        ev
    }
}

pub struct TransferEvent {
    pub sender: Signer,
    pub receiver: Signer,
}

impl From<TransferEvent> for ModuleEvent {
    fn from(ev: TransferEvent) -> Self {
        let TransferEvent { sender, receiver } = ev;
        Self {
            kind: EVENT_TYPE_TRANSFER.to_string(),
            module_name: MODULE_ID_STR.parse().expect("invalid ModuleId"),
            attributes: vec![("sender", sender).into(), ("receiver", receiver).into()],
        }
    }
}

impl From<Event> for ModuleEvent {
    fn from(ev: Event) -> Self {
        match ev {
            Event::Recv(ev) => ev.into(),
            Event::Ack(ev) => ev.into(),
            Event::AckStatus(ev) => ev.into(),
            Event::Timeout(ev) => ev.into(),
            Event::DenomTrace(ev) => ev.into(),
            Event::Transfer(ev) => ev.into(),
        }
    }
}
