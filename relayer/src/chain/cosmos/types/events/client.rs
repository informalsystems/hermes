use ibc::core::ics02_client::error::Error;
use ibc::core::ics02_client::events::{
    Attributes, ClientMisbehaviour, CreateClient, UpdateClient, UpgradeClient,
    CLIENT_ID_ATTRIBUTE_KEY, CLIENT_TYPE_ATTRIBUTE_KEY, CONSENSUS_HEIGHT_ATTRIBUTE_KEY,
    HEADER_ATTRIBUTE_KEY, HEIGHT_ATTRIBUTE_KEY,
};
use ibc::core::ics02_client::header::Header;
use ibc::events::{IbcEvent, IbcEventType};
use tendermint::abci::Event as AbciEvent;

use crate::light_client::AnyHeader;

pub fn try_from_tx(event: &AbciEvent) -> Option<IbcEvent> {
    match event.type_str.parse() {
        Ok(IbcEventType::CreateClient) => extract_attributes_from_tx(event)
            .map(CreateClient)
            .map(IbcEvent::CreateClient)
            .ok(),
        Ok(IbcEventType::UpdateClient) => match extract_attributes_from_tx(event) {
            Ok(attributes) => Some(IbcEvent::UpdateClient(UpdateClient {
                common: attributes,
                header: extract_header_from_tx(event).ok(),
            })),
            Err(_) => None,
        },
        Ok(IbcEventType::ClientMisbehaviour) => extract_attributes_from_tx(event)
            .map(ClientMisbehaviour)
            .map(IbcEvent::ClientMisbehaviour)
            .ok(),
        Ok(IbcEventType::UpgradeClient) => extract_attributes_from_tx(event)
            .map(UpgradeClient)
            .map(IbcEvent::UpgradeClient)
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
                attr.height = value
                    .parse()
                    .map_err(|e| Error::invalid_string_as_height(value.to_string(), e))?
            }
            CLIENT_ID_ATTRIBUTE_KEY => {
                attr.client_id = value.parse().map_err(Error::invalid_client_identifier)?
            }
            CLIENT_TYPE_ATTRIBUTE_KEY => {
                attr.client_type = value
                    .parse()
                    .map_err(|_| Error::unknown_client_type(value.to_string()))?
            }
            CONSENSUS_HEIGHT_ATTRIBUTE_KEY => {
                attr.consensus_height = value
                    .parse()
                    .map_err(|e| Error::invalid_string_as_height(value.to_string(), e))?
            }
            _ => {}
        }
    }

    Ok(attr)
}

pub fn extract_header_from_tx(event: &AbciEvent) -> Result<Box<dyn Header>, Error> {
    for tag in &event.attributes {
        let key = tag.key.as_ref();
        let value = tag.value.as_ref();
        if key == HEADER_ATTRIBUTE_KEY {
            return AnyHeader::decode_from_string(value).map(AnyHeader::into_box);
        }
    }
    Err(Error::missing_raw_header())
}

#[cfg(test)]
mod tests {
    use ibc::core::ics02_client::client_type::ClientType;
    use ibc::mock::header::MockHeader;
    use ibc::Height;

    use super::*;

    #[test]
    fn client_event_to_abci_event() {
        let height = Height::new(1, 1).unwrap();
        let attributes = Attributes {
            height,
            client_id: "test_client".parse().unwrap(),
            client_type: ClientType::Tendermint,
            consensus_height: height,
        };
        let mut abci_events = vec![];
        let create_client = CreateClient::from(attributes.clone());
        abci_events.push(AbciEvent::from(create_client.clone()));
        let client_misbehaviour = ClientMisbehaviour::from(attributes.clone());
        abci_events.push(AbciEvent::from(client_misbehaviour.clone()));
        let upgrade_client = UpgradeClient::from(attributes.clone());
        abci_events.push(AbciEvent::from(upgrade_client.clone()));
        let mut update_client = UpdateClient::from(attributes);
        let header = AnyHeader::Mock(MockHeader::new(height));
        update_client.header = Some(header.into_box());
        abci_events.push(AbciEvent::from(update_client.clone()));

        for event in abci_events {
            match try_from_tx(&event) {
                Some(e) => match e {
                    IbcEvent::CreateClient(e) => assert_eq!(e.0, create_client.0),
                    IbcEvent::ClientMisbehaviour(e) => assert_eq!(e.0, client_misbehaviour.0),
                    IbcEvent::UpgradeClient(e) => assert_eq!(e.0, upgrade_client.0),
                    IbcEvent::UpdateClient(e) => {
                        assert_eq!(e.common, update_client.common);
                        assert_eq!(e.header, update_client.header);
                    }
                    _ => panic!("unexpected event type"),
                },
                None => panic!("converted event was wrong"),
            }
        }
    }
}
