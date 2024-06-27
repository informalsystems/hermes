
use ibc_relayer_types::core::ics03_connection::events::OpenInit;
use ibc_relayer_types::core::ics03_connection::events::OpenTry;
use ibc_relayer_types::core::ics03_connection::events::OpenAck;
use ibc_relayer_types::core::ics03_connection::events::OpenConfirm;
use ibc_relayer_types::core::ics03_connection::events::Attributes;
use ibc_relayer_types::events::Error as EventError;
use ibc_relayer_types::core::ics04_channel::events::EventType;

use crate::chain::cosmos::types::events::raw_object::RawObject;
use crate::chain::cosmos::types::events::raw_object::extract_attribute;
use crate::chain::cosmos::types::events::raw_object::maybe_extract_attribute;

fn extract_attributes(object: &RawObject<'_>, namespace: &str) -> Result<Attributes, EventError> {
    Ok(Attributes {
        client_id: extract_attribute(object, &format!("{namespace}.client_id"))?
            .parse()
            .map_err(EventError::parse)?,
        counterparty_connection_id: maybe_extract_attribute(
            object,
            &format!("{namespace}.counterparty_connection_id"),
        )
        .and_then(|v| v.parse().ok()),
        counterparty_client_id: extract_attribute(object, &format!("{namespace}.counterparty_client_id"))?
            .parse()
            .map_err(EventError::parse)?,
        connection_id: maybe_extract_attribute(
            object,
            &format!("{namespace}.connection_id"),
        )
        .and_then(|v| v.parse().ok()),
    })
}

impl TryFrom<RawObject<'_>> for OpenInit {
    type Error = EventError;

    fn try_from(value: RawObject<'_>) -> Result<Self, Self::Error> {
        let attributes = extract_attributes(&value, Self::event_type().as_str())?;
        Ok(OpenInit(attributes))
    }
}

impl TryFrom<RawObject<'_>> for OpenTry {
    type Error = EventError;

    fn try_from(value: RawObject<'_>) -> Result<Self, Self::Error> {
        let attributes = extract_attributes(&value, Self::event_type().as_str())?;
        Ok(OpenTry(attributes))
    }
}

impl TryFrom<RawObject<'_>> for OpenAck {
    type Error = EventError;

    fn try_from(value: RawObject<'_>) -> Result<Self, Self::Error> {
        let attributes = extract_attributes(&value, Self::event_type().as_str())?;
        Ok(OpenAck(attributes))
    }
}

impl TryFrom<RawObject<'_>> for OpenConfirm {
    type Error = EventError;

    fn try_from(value: RawObject<'_>) -> Result<Self, Self::Error> {
        let attributes = extract_attributes(&value, Self::event_type().as_str())?;
        Ok(OpenConfirm(attributes))
    }
}