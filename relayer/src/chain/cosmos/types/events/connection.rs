use ibc::core::ics02_client::error::Error as Ics02Error;
use ibc::core::ics03_connection::error::Error;
use ibc::core::ics03_connection::events::{
    Attributes, OpenAck, OpenConfirm, OpenInit, OpenTry, CLIENT_ID_ATTRIBUTE_KEY,
    CONN_ID_ATTRIBUTE_KEY, COUNTERPARTY_CLIENT_ID_ATTRIBUTE_KEY,
    COUNTERPARTY_CONN_ID_ATTRIBUTE_KEY, HEIGHT_ATTRIBUTE_KEY,
};
use ibc::events::{IbcEvent, IbcEventType};
use tendermint::abci::Event as AbciEvent;

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
    use ibc::core::ics03_connection::events::Attributes;
    use ibc::Height;

    use super::*;

    #[test]
    fn connection_event_to_abci_event() {
        let height = Height::new(1, 1).unwrap();
        let attributes = Attributes {
            height,
            connection_id: Some("test_connection".parse().unwrap()),
            client_id: "test_client".parse().unwrap(),
            counterparty_connection_id: Some("counterparty_test_conn".parse().unwrap()),
            counterparty_client_id: "counterparty_test_client".parse().unwrap(),
        };
        let mut abci_events = vec![];
        let open_init = OpenInit::from(attributes.clone());
        abci_events.push(AbciEvent::from(open_init.clone()));
        let open_try = OpenTry::from(attributes.clone());
        abci_events.push(AbciEvent::from(open_try.clone()));
        let open_ack = OpenAck::from(attributes.clone());
        abci_events.push(AbciEvent::from(open_ack.clone()));
        let open_confirm = OpenConfirm::from(attributes);
        abci_events.push(AbciEvent::from(open_confirm.clone()));

        for event in abci_events {
            match try_from_tx(&event) {
                Some(e) => match e {
                    IbcEvent::OpenInitConnection(e) => assert_eq!(e, open_init),
                    IbcEvent::OpenTryConnection(e) => assert_eq!(e, open_try),
                    IbcEvent::OpenAckConnection(e) => assert_eq!(e, open_ack),
                    IbcEvent::OpenConfirmConnection(e) => assert_eq!(e, open_confirm),
                    _ => panic!("unexpected event type"),
                },
                None => panic!("converted event was wrong"),
            }
        }
    }
}
