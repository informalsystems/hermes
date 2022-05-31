//! ABCI event parsing for the IBC events emitted from Tendermint Websocket by the client module.

use tendermint_rpc::abci::Event as AbciEvent;

use ibc::core::ics02_client::error::Error;
use ibc::core::ics02_client::events::{
    Attributes, ClientMisbehaviour, CreateClient, UpdateClient, UpgradeClient,
};
use ibc::core::ics02_client::header::AnyHeader;
use ibc::events::{IbcEvent, IbcEventType};

/// The content of the `key` field for the attribute containing the height.
const HEIGHT_ATTRIBUTE_KEY: &str = "height";

/// The content of the `key` field for the attribute containing the client identifier.
const CLIENT_ID_ATTRIBUTE_KEY: &str = "client_id";

/// The content of the `key` field for the attribute containing the client type.
const CLIENT_TYPE_ATTRIBUTE_KEY: &str = "client_type";

/// The content of the `key` field for the attribute containing the height.
const CONSENSUS_HEIGHT_ATTRIBUTE_KEY: &str = "consensus_height";

/// The content of the `key` field for the header in update client event.
const HEADER_ATTRIBUTE_KEY: &str = "header";

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

pub fn extract_header_from_tx(event: &AbciEvent) -> Result<AnyHeader, Error> {
    for tag in &event.attributes {
        let key = tag.key.as_ref();
        let value = tag.value.as_ref();
        if key == HEADER_ATTRIBUTE_KEY {
            return AnyHeader::decode_from_string(value);
        }
    }
    Err(Error::missing_raw_header())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::event::ToAbciEvent;
    use ibc::core::ics02_client::client_type::ClientType;
    use ibc::core::ics02_client::header::Header;
    use ibc::core::ics02_client::height::Height;
    use ibc::mock::header::MockHeader;
    use tendermint_rpc::abci::tag::Tag;

    impl ToAbciEvent for CreateClient {
        fn to_abci_event(&self) -> AbciEvent {
            let attributes = attributes_to_abci_tags(&self.0);
            AbciEvent {
                type_str: IbcEventType::CreateClient.as_str().to_string(),
                attributes,
            }
        }
    }

    impl ToAbciEvent for UpdateClient {
        fn to_abci_event(&self) -> AbciEvent {
            let mut attributes = attributes_to_abci_tags(&self.common);
            if let Some(h) = &self.header {
                let header = Tag {
                    key: HEADER_ATTRIBUTE_KEY.parse().unwrap(),
                    value: h.encode_to_string().parse().unwrap(),
                };
                attributes.push(header);
            }
            AbciEvent {
                type_str: IbcEventType::UpdateClient.as_str().to_string(),
                attributes,
            }
        }
    }

    impl ToAbciEvent for ClientMisbehaviour {
        fn to_abci_event(&self) -> AbciEvent {
            let attributes = attributes_to_abci_tags(&self.0);
            AbciEvent {
                type_str: IbcEventType::ClientMisbehaviour.as_str().to_string(),
                attributes,
            }
        }
    }

    impl ToAbciEvent for UpgradeClient {
        fn to_abci_event(&self) -> AbciEvent {
            let attributes = attributes_to_abci_tags(&self.0);
            AbciEvent {
                type_str: IbcEventType::UpgradeClient.as_str().to_string(),
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
        let height = Tag {
            key: HEIGHT_ATTRIBUTE_KEY.parse().unwrap(),
            value: a.height.to_string().parse().unwrap(),
        };
        let client_id = Tag {
            key: CLIENT_ID_ATTRIBUTE_KEY.parse().unwrap(),
            value: a.client_id.to_string().parse().unwrap(),
        };
        let client_type = Tag {
            key: CLIENT_TYPE_ATTRIBUTE_KEY.parse().unwrap(),
            value: a.client_type.as_str().parse().unwrap(),
        };
        let consensus_height = Tag {
            key: CONSENSUS_HEIGHT_ATTRIBUTE_KEY.parse().unwrap(),
            value: a.height.to_string().parse().unwrap(),
        };
        vec![height, client_id, client_type, consensus_height]
    }

    #[test]
    fn client_event_to_abci_event() {
        let height = Height::new(1, 1);
        let attributes = Attributes {
            height,
            client_id: "test_client".parse().unwrap(),
            client_type: ClientType::Tendermint,
            consensus_height: height,
        };
        let mut abci_events = vec![];
        let create_client = CreateClient::from(attributes.clone());
        abci_events.push(create_client.to_abci_event());
        let client_misbehaviour = ClientMisbehaviour::from(attributes.clone());
        abci_events.push(client_misbehaviour.to_abci_event());
        let upgrade_client = UpgradeClient::from(attributes.clone());
        abci_events.push(upgrade_client.to_abci_event());
        let mut update_client = UpdateClient::from(attributes);
        let header = MockHeader::new(height).wrap_any();
        update_client.header = Some(header);
        abci_events.push(update_client.to_abci_event());

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
