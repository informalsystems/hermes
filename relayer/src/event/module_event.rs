use ibc::events::{IbcEventType, ModuleEvent, ModuleEventAttribute};
use tendermint_rpc::abci::tag::Tag;
use tendermint_rpc::abci::Event as AbciEvent;

use super::ToAbciEvent;

// TODO: this is test support code, now add some tests

impl ToAbciEvent for ModuleEvent {
    fn to_abci_event(&self) -> AbciEvent {
        if self.kind.parse::<IbcEventType>().is_ok() {
            panic!("module event cannot use core event types: {:?}", self);
        }

        let attributes = self.attributes.iter().map(attribute_to_abci_tag).collect();
        AbciEvent {
            type_str: self.kind.clone(),
            attributes,
        }
    }
}

fn attribute_to_abci_tag(attr: &ModuleEventAttribute) -> Tag {
    Tag {
        key: attr
            .key
            .parse()
            .expect("Key::from_str() impl is infallible"),
        value: attr
            .value
            .parse()
            .expect("Value::from_str() impl is infallible"),
    }
}
