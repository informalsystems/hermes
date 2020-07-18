use super::exported::*;
use crate::ics04_channel::error;
use crate::ics04_channel::error::{Error, Kind};
use crate::ics24_host::identifier::{ChannelId, ConnectionId, PortId};
use crate::try_from_raw::TryFromRaw;
use serde_derive::{Deserialize, Serialize};

// Import proto declarations.
use ibc_proto::channel::Channel as RawChannel;

use std::str::FromStr;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ChannelEnd {
    state: State,
    ordering: Order,
    remote: Counterparty,
    connection_hops: Vec<ConnectionId>,
    version: String,
}

impl TryFromRaw for ChannelEnd {
    type RawType = RawChannel;
    type Error = anomaly::Error<Kind>;
    fn try_from(value: RawChannel) -> Result<Self, Self::Error> {
        // Todo: Do validation of data here. This is just an example implementation for testing.
        let ordering = match value.ordering {
            0 => Order::None,
            1 => Order::Unordered,
            2 => Order::Ordered,
            _ => panic!("invalid order number"),
        };
        let counterparty = value.counterparty.unwrap();
        let remote = Counterparty {
            port_id: PortId::from_str(counterparty.port_id.as_str()).unwrap(),
            channel_id: ChannelId::from_str(counterparty.channel_id.as_str()).unwrap(),
        };
        let connection_hops = value
            .connection_hops
            .into_iter()
            .map(|e| ConnectionId::from_str(e.as_str()).unwrap())
            .collect();
        let version = value.version;
        Ok(ChannelEnd::new(ordering, remote, connection_hops, version))
    }
}

impl ChannelEnd {
    pub fn new(
        ordering: Order,
        remote: Counterparty,
        connection_hops: Vec<ConnectionId>,
        version: String,
    ) -> Self {
        Self {
            state: State::Uninitialized,
            ordering,
            remote,
            connection_hops,
            version,
        }
    }
}

impl Channel for ChannelEnd {
    type ValidationError = Error;

    fn state(&self) -> &State {
        &self.state
    }

    fn ordering(&self) -> &Order {
        &self.ordering
    }

    fn counterparty(
        &self,
    ) -> Box<dyn ChannelCounterparty<ValidationError = Self::ValidationError>> {
        Box::new(self.remote.clone())
    }

    fn connection_hops(&self) -> Vec<ConnectionId> {
        self.connection_hops.clone()
    }

    fn version(&self) -> String {
        self.version.parse().unwrap()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        if self.connection_hops.len() != 1 {
            return Err(error::Kind::InvalidConnectionHopsLength
                .context("validate channel")
                .into());
        }
        if self.version().trim() == "" {
            return Err(error::Kind::InvalidVersion
                .context("empty version string")
                .into());
        }
        self.counterparty().validate_basic()
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Counterparty {
    port_id: PortId,
    channel_id: ChannelId,
}

impl Counterparty {
    pub fn new(port_id: String, channel_id: String) -> Result<Self, Error> {
        Ok(Self {
            port_id: port_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
            channel_id: channel_id
                .parse()
                .map_err(|e| Kind::IdentifierError.context(e))?,
        })
    }
}

impl ChannelCounterparty for Counterparty {
    type ValidationError = Error;

    fn port_id(&self) -> String {
        self.port_id.as_str().into()
    }

    fn channel_id(&self) -> String {
        self.channel_id.as_str().into()
    }

    fn validate_basic(&self) -> Result<(), Self::ValidationError> {
        Ok(())
    }
}
