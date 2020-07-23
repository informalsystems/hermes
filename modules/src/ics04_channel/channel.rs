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
        // Parse the ordering type. Propagate the error, if any, to our caller.
        let chan_ordering = Order::from_i32(value.ordering)?;

        let chan_state = State::from_i32(value.state)?;

        // Pop out the Counterparty from the Option.
        let counterparty = match value.counterparty {
            Some(cp) => cp,
            None => return Err(Kind::MissingCounterparty.into()),
        };

        // Assemble the 'remote' attribute of the Channel, which represents the Counterparty.
        let remote = Counterparty {
            port_id: PortId::from_str(counterparty.port_id.as_str())
                .map_err(|e| Kind::IdentifierError.context(e))?,
            channel_id: ChannelId::from_str(counterparty.channel_id.as_str())
                .map_err(|e| Kind::IdentifierError.context(e))?,
        };

        // Parse each item in connection_hops into a ConnectionId.
        let connection_hops = value
            .connection_hops
            .into_iter()
            .map(|conn_id| ConnectionId::from_str(conn_id.as_str()))
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| Kind::IdentifierError.context(e))?;

        // This field is supposed to be opaque to the core IBC protocol. Empty
        // version is allowed by the specification (cf. ICS 004). No explicit validation necessary.
        let version = value.version;

        let mut channel_end = ChannelEnd::new(chan_ordering, remote, connection_hops, version);
        channel_end.set_state(chan_state);

        Ok(channel_end)
    }
}

impl ChannelEnd {
    /// Creates a new ChannelEnd in state Uninitialized and other fields parametrized.
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

    /// Updates the ChannelEnd to assume a new State 's'.
    pub fn set_state(&mut self, s: State) {
        self.state = s;
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

#[cfg(test)]
mod tests {
    use crate::ics04_channel::channel::ChannelEnd;
    use crate::try_from_raw::TryFromRaw;
    use ibc_proto::channel::Channel as RawChannel;
    use ibc_proto::channel::Counterparty as RawCounterparty;

    #[test]
    fn channel_end_try_from_raw() {
        let empty_raw_channel_end = RawChannel {
            state: 0,
            ordering: 0,
            counterparty: None,
            connection_hops: vec![],
            version: "".to_string(),
        };

        let cparty = RawCounterparty {
            port_id: "0123456789".into(),
            channel_id: "0987654321".into(),
        };

        let raw_channel_end = RawChannel {
            state: 0,
            ordering: 0,
            counterparty: Some(cparty),
            connection_hops: vec![],
            version: "".to_string(), // The version is not validated.
        };

        struct Test {
            name: String,
            params: RawChannel,
            want_pass: bool,
        }

        let tests: Vec<Test> = vec![
            Test {
                name: "Raw channel end with missing counterparty".to_string(),
                params: empty_raw_channel_end.clone(),
                want_pass: false,
            },
            Test {
                name: "Raw channel end with incorrect state".to_string(),
                params: RawChannel {
                    state: -1,
                    ..raw_channel_end.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Raw channel end with incorrect ordering".to_string(),
                params: RawChannel {
                    ordering: -1,
                    ..raw_channel_end.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Raw channel end with incorrect connection id in connection hops".to_string(),
                params: RawChannel {
                    connection_hops: vec!["connection*".to_string()].into_iter().collect(),
                    ..raw_channel_end.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Raw channel end with incorrect connection id (has blank space)".to_string(),
                params: RawChannel {
                    connection_hops: vec!["con nection".to_string()].into_iter().collect(),
                    ..raw_channel_end.clone()
                },
                want_pass: false,
            },
            Test {
                name: "Raw channel end with two correct connection ids in connection hops"
                    .to_string(),
                params: RawChannel {
                    connection_hops: vec!["connection1".to_string(), "connection2".to_string()]
                        .into_iter()
                        .collect(),
                    ..raw_channel_end.clone()
                },
                want_pass: true,
            },
            Test {
                name: "Raw channel end with correct params".to_string(),
                params: raw_channel_end.clone(),
                want_pass: true,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let p = test.params.clone();

            let ce_result = ChannelEnd::try_from(p);

            assert_eq!(
                test.want_pass,
                ce_result.is_ok(),
                "ChannelEnd::try_from() failed for test {}, \nmsg{:?} with error {:?}",
                test.name,
                test.params.clone(),
                ce_result.err(),
            );
        }
    }
}
