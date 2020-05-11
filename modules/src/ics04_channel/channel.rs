use super::exported::*;
use crate::ics24_host::identifier::{ChannelId, PortId};
use serde_derive::{Deserialize, Serialize};
//use crate::ics24_host::error::ValidationError;
use super::error;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Channel {
    state: State,
    ordering: Order,
    remote: Endpoint,
    connection_hops: Vec<String>,
    version: String,
}

impl Channel {
    pub fn new(
        ordering: Order,
        remote: Endpoint,
        connection_hops: Vec<String>,
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

impl ChannelI for Channel {
    type ValidationError = error::Error;

    fn state(&self) -> State {
        self.state.clone()
    }

    fn ordering(&self) -> Order {
        self.ordering.clone()
    }

    fn counterparty(&self) -> Box<dyn CounterpartyI<ValidationError = super::error::Error>> {
        Box::new(self.remote.clone())
    }

    fn connection_hops(&self) -> Vec<String> {
        self.connection_hops.clone()
    }

    fn version(&self) -> String {
        self.version.parse().unwrap()
    }

    //fn validate_basic(&self) -> Result<(), ValidationError> {
    //    Ok(())
    //}
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Endpoint {
    port_id: PortId,
    channel_id: ChannelId,
}

impl Endpoint {
    pub fn new(port_id: String, channel_id: String) -> Self {
        Self {
            port_id: port_id.parse().unwrap(),
            channel_id: channel_id.parse().unwrap(),
        }
    }
}

impl CounterpartyI for Endpoint {
    type ValidationError = error::Error;

    fn port_id(&self) -> String {
        String::from(self.port_id.as_str())
    }

    fn channel_id(&self) -> String {
        String::from(self.channel_id.as_str())
    }

    //fn validate_basic(&self) -> Result<(), ValidationError> {
    // Ok(())
    //}
}
