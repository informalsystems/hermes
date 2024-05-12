use ibc_relayer_types::core::ics02_client::error::Error;
use ibc_relayer_types::core::ics02_client::events::{
    Attributes, ClientMisbehaviour, CreateClient, UpdateClient, UpgradeClient,
    CLIENT_ID_ATTRIBUTE_KEY, CLIENT_TYPE_ATTRIBUTE_KEY, CONSENSUS_HEIGHT_ATTRIBUTE_KEY,
    HEADER_ATTRIBUTE_KEY, HEIGHT_ATTRIBUTE_KEY,
};
use ibc_relayer_types::core::ics02_client::header::Header;
use ibc_relayer_types::events::{IbcEvent, IbcEventType};
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
