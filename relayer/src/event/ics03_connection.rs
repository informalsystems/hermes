//! ABCI event parsing for the IBC events emitted from Tendermint Websocket by the connection module.

use ibc::core::ics02_client::error::Error as Ics02Error;
use ibc::core::ics03_connection::error::Error;
use ibc::core::ics03_connection::events::{Attributes, OpenAck, OpenConfirm, OpenInit, OpenTry};
use ibc::events::{IbcEvent, IbcEventType};
use tendermint_rpc::abci::Event as AbciEvent;

/// The content of the `key` field for the attribute containing the connection identifier.
const HEIGHT_ATTRIBUTE_KEY: &str = "height";
const CONN_ID_ATTRIBUTE_KEY: &str = "connection_id";
const CLIENT_ID_ATTRIBUTE_KEY: &str = "client_id";
const COUNTERPARTY_CONN_ID_ATTRIBUTE_KEY: &str = "counterparty_connection_id";
const COUNTERPARTY_CLIENT_ID_ATTRIBUTE_KEY: &str = "counterparty_client_id";

pub fn try_from_tx(event: &AbciEvent) -> Option<IbcEvent> {
    match event.type_str.parse() {
        Ok(IbcEventType::OpenInitConnection) => extract_attributes_from_tx(event)
            .map(OpenInit::from)
            .map(IbcEvent::OpenInitConnection)
            .ok(),
        Ok(IbcEventType::OpenTryConnection) => extract_attributes_from_tx(event)
            .map(OpenTry::from)
            .map(IbcEvent::OpenTryConnection)
            .ok(),
        Ok(IbcEventType::OpenAckConnection) => extract_attributes_from_tx(event)
            .map(OpenAck::from)
            .map(IbcEvent::OpenAckConnection)
            .ok(),
        Ok(IbcEventType::OpenConfirmConnection) => extract_attributes_from_tx(event)
            .map(OpenConfirm::from)
            .map(IbcEvent::OpenConfirmConnection)
            .ok(),
        _ => None,
    }
}

fn extract_attributes_from_tx(event: &AbciEvent) -> Result<Attributes, Error> {
    let mut attr = Attributes::default();

    for tag in &event.attributes {
        let key = tag.key.as_ref();
        let value = tag.value.as_ref();
        match key {
            HEIGHT_ATTRIBUTE_KEY => {
                attr.height = value.parse().map_err(|e| {
                    Error::ics02_client(Ics02Error::invalid_string_as_height(value.to_string(), e))
                })?;
            }
            CONN_ID_ATTRIBUTE_KEY => {
                attr.connection_id = value.parse().ok();
            }
            CLIENT_ID_ATTRIBUTE_KEY => {
                attr.client_id = value.parse().map_err(Error::invalid_identifier)?;
            }
            COUNTERPARTY_CONN_ID_ATTRIBUTE_KEY => {
                attr.counterparty_connection_id = value.parse().ok();
            }
            COUNTERPARTY_CLIENT_ID_ATTRIBUTE_KEY => {
                attr.counterparty_client_id = value.parse().map_err(Error::invalid_identifier)?;
            }
            _ => {}
        }
    }

    Ok(attr)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::event::ToAbciEvent;
    use ibc::core::ics02_client::height::Height;
    use tendermint_rpc::abci::tag::Tag;

    impl ToAbciEvent for OpenInit {
        fn to_abci_event(&self) -> AbciEvent {
            let attributes = attributes_to_abci_tags(self.attributes());
            AbciEvent {
                type_str: IbcEventType::OpenInitConnection.as_str().to_string(),
                attributes,
            }
        }
    }

    impl ToAbciEvent for OpenTry {
        fn to_abci_event(&self) -> AbciEvent {
            let attributes = attributes_to_abci_tags(self.attributes());
            AbciEvent {
                type_str: IbcEventType::OpenTryConnection.as_str().to_string(),
                attributes,
            }
        }
    }

    impl ToAbciEvent for OpenAck {
        fn to_abci_event(&self) -> AbciEvent {
            let attributes = attributes_to_abci_tags(self.attributes());
            AbciEvent {
                type_str: IbcEventType::OpenAckConnection.as_str().to_string(),
                attributes,
            }
        }
    }

    impl ToAbciEvent for OpenConfirm {
        fn to_abci_event(&self) -> AbciEvent {
            let attributes = attributes_to_abci_tags(self.attributes());
            AbciEvent {
                type_str: IbcEventType::OpenConfirmConnection.as_str().to_string(),
                attributes,
            }
        }
    }

    /// Convert attributes to Tendermint ABCI tags
    ///
    /// # Note
    /// The parsing of `Key`s and `Value`s never fails, because the
    /// `FromStr` instance of `tendermint::abci::tag::{Key, Value}`
    /// is infallible, even if it is not represented in the error type.
    /// Once tendermint-rs improves the API of the `Key` and `Value` types,
    /// we will be able to remove the `.parse().unwrap()` calls.
    fn attributes_to_abci_tags(a: &Attributes) -> Vec<Tag> {
        let mut attributes = vec![];
        let height = Tag {
            key: HEIGHT_ATTRIBUTE_KEY.parse().unwrap(),
            value: a.height.to_string().parse().unwrap(),
        };
        attributes.push(height);
        if let Some(conn_id) = &a.connection_id {
            let conn_id = Tag {
                key: CONN_ID_ATTRIBUTE_KEY.parse().unwrap(),
                value: conn_id.to_string().parse().unwrap(),
            };
            attributes.push(conn_id);
        }
        let client_id = Tag {
            key: CLIENT_ID_ATTRIBUTE_KEY.parse().unwrap(),
            value: a.client_id.to_string().parse().unwrap(),
        };
        attributes.push(client_id);
        if let Some(conn_id) = &a.counterparty_connection_id {
            let conn_id = Tag {
                key: COUNTERPARTY_CONN_ID_ATTRIBUTE_KEY.parse().unwrap(),
                value: conn_id.to_string().parse().unwrap(),
            };
            attributes.push(conn_id);
        }
        let counterparty_client_id = Tag {
            key: COUNTERPARTY_CLIENT_ID_ATTRIBUTE_KEY.parse().unwrap(),
            value: a.counterparty_client_id.to_string().parse().unwrap(),
        };
        attributes.push(counterparty_client_id);
        attributes
    }

    #[test]
    fn connection_event_to_abci_event() {
        let height = Height::new(1, 1);
        let attributes = Attributes {
            height,
            connection_id: Some("test_connection".parse().unwrap()),
            client_id: "test_client".parse().unwrap(),
            counterparty_connection_id: Some("counterparty_test_conn".parse().unwrap()),
            counterparty_client_id: "counterparty_test_client".parse().unwrap(),
        };
        let mut abci_events = vec![];
        let open_init = OpenInit::from(attributes.clone());
        abci_events.push(open_init.to_abci_event());
        let open_try = OpenTry::from(attributes.clone());
        abci_events.push(open_try.to_abci_event());
        let open_ack = OpenAck::from(attributes.clone());
        abci_events.push(open_ack.to_abci_event());
        let open_confirm = OpenConfirm::from(attributes);
        abci_events.push(open_confirm.to_abci_event());

        for event in abci_events {
            match try_from_tx(&event) {
                Some(e) => match e {
                    IbcEvent::OpenInitConnection(e) => {
                        assert_eq!(e.attributes(), open_init.attributes())
                    }
                    IbcEvent::OpenTryConnection(e) => {
                        assert_eq!(e.attributes(), open_try.attributes())
                    }
                    IbcEvent::OpenAckConnection(e) => {
                        assert_eq!(e.attributes(), open_ack.attributes())
                    }
                    IbcEvent::OpenConfirmConnection(e) => {
                        assert_eq!(e.attributes(), open_confirm.attributes())
                    }
                    _ => panic!("unexpected event type"),
                },
                None => panic!("converted event was wrong"),
            }
        }
    }
}
