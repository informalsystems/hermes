//! Types for the IBC events emitted from Tendermint Websocket for the connection modules.

use serde_json::Value;
use std::convert::TryFrom;
use tendermint::rpc::event_listener::Event;

pub struct ConnectionOpenInitEvent {
    data: Value,
}

impl TryFrom<Event> for ConnectionOpenInitEvent {
    type Error = &'static str;
    fn try_from(event: Event) -> Result<Self, Self::Error> {
        match event {
            Event::GenericJSONEvent { ref data } => match data {
                Value::Object(obj) => {
                    if obj["type"].as_str() == Some("connection_open_init") {
                        return Ok(ConnectionOpenInitEvent { data: data.clone() });
                    }
                    Err("Expected JSON respresenting a ConnectionOpenInit, got wrong type")?
                }
                _ => Err("Expected JSON representing a ConnectionOpenInit, got wrong type"),
            },
            Event::GenericStringEvent { .. } => {
                Err("Generic event is not of type connection open init")
            }
        }
    }
}

pub struct ConnectionOpenTryEvent {
    data: Value,
}

impl TryFrom<Event> for ConnectionOpenTryEvent {
    type Error = &'static str;
    fn try_from(event: Event) -> Result<Self, Self::Error> {
        match event {
            Event::GenericJSONEvent { ref data } => match data {
                Value::Object(obj) => {
                    if obj["type"].as_str() == Some("connection_open_try") {
                        return Ok(ConnectionOpenTryEvent { data: data.clone() });
                    }
                    Err("Expected JSON respresenting a ConnectionOpenTry, got wrong type")?
                }
                _ => Err("Expected JSON representing a ConnectionOpenTry, got wrong type"),
            },
            Event::GenericStringEvent { .. } => {
                Err("Generic event is not of type connection open try")
            }
        }
    }
}

pub struct ConnectionOpenAckEvent {
    data: Value,
}

impl TryFrom<Event> for ConnectionOpenAckEvent {
    type Error = &'static str;
    fn try_from(event: Event) -> Result<Self, Self::Error> {
        match event {
            Event::GenericJSONEvent { ref data } => match data {
                Value::Object(obj) => {
                    if obj["type"].as_str() == Some("connection_open_ack") {
                        return Ok(ConnectionOpenAckEvent { data: data.clone() });
                    }
                    Err("Expected JSON respresenting a ConnectionOpenAck, got wrong type")?
                }
                _ => Err("Expected JSON representing a ConnectionOpenAck, got wrong type"),
            },
            Event::GenericStringEvent { .. } => {
                Err("Generic event is not of type connection open ack")
            }
        }
    }
}

pub struct ConnectionOpenConfirmEvent {
    data: Value,
}

impl TryFrom<Event> for ConnectionOpenConfirmEvent {
    type Error = &'static str;
    fn try_from(event: Event) -> Result<Self, Self::Error> {
        match event {
            Event::GenericJSONEvent { ref data } => match data {
                Value::Object(obj) => {
                    if obj["type"].as_str() == Some("connection_open_confirm") {
                        return Ok(ConnectionOpenConfirmEvent { data: data.clone() });
                    }
                    Err("Expected JSON respresenting a ConnectionOpenConfirm, got wrong type")?
                }
                _ => Err("Expected JSON representing a ConnectionOpenConfirm, got wrong type"),
            },
            Event::GenericStringEvent { .. } => {
                Err("Generic event is not of type connection open confirm")
            }
        }
    }
}
