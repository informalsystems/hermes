//! Types for the IBC events emitted from Tendermint Websocket for the client modules.

use serde_json::Value;
use std::convert::TryFrom;
use tendermint::rpc::event_listener::Event;

pub struct CreateClientEvent {
    data: Value,
}

impl TryFrom<Event> for CreateClientEvent {
    type Error = &'static str;
    fn try_from(event: Event) -> Result<Self, Self::Error> {
        match event {
            Event::GenericJSONEvent { ref data } => match data {
                Value::Object(obj) => {
                    if obj["type"].as_str() == Some("create_client") {
                        return Ok(CreateClientEvent { data: data.clone() });
                    }
                    Err("Expected JSON representing a CreateClient, got wrong type")?
                }
                _ => Err("Expected JSON representing a CreateClient, got wrong type")?,
            },
            Event::GenericStringEvent { .. } => Err("Generic event is not of type create client"),
        }
    }
}

struct UpdateClientEvent {
    data: Value,
}

impl TryFrom<Event> for UpdateClientEvent {
    type Error = &'static str;
    fn try_from(event: Event) -> Result<Self, Self::Error> {
        match event {
            Event::GenericJSONEvent { ref data } => match data {
                Value::Object(obj) => {
                    if obj["type"].as_str() == Some("update_client") {
                        return Ok(UpdateClientEvent { data: data.clone() });
                    }
                    Err("Expected JSON respresenting an UpdateClient, got wrong type")?
                }
                _ => Err("Expected JSON representing an UpdateClient, got wrong type"),
            },
            Event::GenericStringEvent { .. } => Err("Generic event is not of type update client"),
        }
    }
}

struct MessageEvent {
    data: Value,
}

impl TryFrom<Event> for MessageEvent {
    type Error = &'static str;
    fn try_from(event: Event) -> Result<Self, Self::Error> {
        match event {
            Event::GenericJSONEvent { ref data } => match data {
                Value::Object(obj) => {
                    if obj["type"].as_str() == Some("message") {
                        return Ok(MessageEvent { data: data.clone() });
                    }
                    Err("Expected JSON respresenting a Message, got wrong type")?
                }
                _ => Err("Expected JSON representing a Message, got wrong type"),
            },
            Event::GenericStringEvent { .. } => Err("Generic event is not of type message"),
        }
    }
}

struct SubmitMisbehaviourEvent {
    data: Value,
}

impl TryFrom<Event> for SubmitMisbehaviourEvent {
    type Error = &'static str;
    fn try_from(event: Event) -> Result<Self, Self::Error> {
        match event {
            Event::GenericJSONEvent { ref data } => match data {
                Value::Object(obj) => {
                    if obj["type"].as_str() == Some("submit_misbehaviour") {
                        return Ok(SubmitMisbehaviourEvent { data: data.clone() });
                    }
                    Err("Expected JSON respresenting a SubmitMisbehaviour, got wrong type")?
                }
                _ => Err("Expected JSON representing a SubmitMisbehavior, got wrong type"),
            },
            Event::GenericStringEvent { .. } => {
                Err("Generic event is not of type submit misbehaviour")
            }
        }
    }
}

struct ConnectionOpenInitEvent {
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

struct ConnectionOpenTryEvent {
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
