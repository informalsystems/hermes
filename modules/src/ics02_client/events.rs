//! Types for the IBC events emitted from Tendermint Websocket for the client modules.

// use serde_json::Value;
use std::convert::TryFrom;
use tendermint::rpc::event_listener::Event;
use serde_derive::{Deserialize, Serialize};
#[derive(Debug, Deserialize,Serialize)]
pub struct CreateClientEvent {
    events: std::collections::HashMap<String, Vec<String>>
}

impl TryFrom<Event> for CreateClientEvent {
    type Error = &'static str;
    fn try_from(event: Event) -> Result<Self, Self::Error> {
        dbg!(&event);
        match event {
            Event::JsonRPCTransctionResult{ref data}=>{
                Ok(CreateClientEvent{events: data.extract_events("ibc_client","create_client")?})
            },
            Event::GenericJSONEvent { .. } => {
                    Err("Expected JSON representing a CreateClient, got wrong type")?
                },
            
            Event::GenericStringEvent { .. } => Err("Generic event is not of type create client"),   
        }
    }
}

// pub struct UpdateClientEvent {
//     data: Value,
// }

// impl TryFrom<Event> for UpdateClientEvent {
//     type Error = &'static str;
//     fn try_from(event: Event) -> Result<Self, Self::Error> {
//         match event {
//             Event::GenericJSONEvent { ref data } => match data {
//                 Value::Object(obj) => {
//                     if obj["type"].as_str() == Some("update_client") {
//                         return Ok(UpdateClientEvent { data: data.clone() });
//                     }
//                     Err("Expected JSON respresenting an UpdateClient, got wrong type")?
//                 }
//                 _ => Err("Expected JSON representing an UpdateClient, got wrong type"),
//             },
//             Event::GenericStringEvent { .. } => Err("Generic event is not of type update client"),
//         }
//     }
// }

// pub struct SubmitMisbehaviourEvent {
//     data: Value,
// }

// impl TryFrom<Event> for SubmitMisbehaviourEvent {
//     type Error = &'static str;
//     fn try_from(event: Event) -> Result<Self, Self::Error> {
//         match event {
//             Event::GenericJSONEvent { ref data } => match data {
//                 Value::Object(obj) => {
//                     if obj["type"].as_str() == Some("submit_misbehaviour") {
//                         return Ok(SubmitMisbehaviourEvent { data: data.clone() });
//                     }
//                     Err("Expected JSON respresenting a SubmitMisbehaviour, got wrong type")?
//                 }
//                 _ => Err("Expected JSON representing a SubmitMisbehavior, got wrong type"),
//             },
//             Event::GenericStringEvent { .. } => {
//                 Err("Generic event is not of type submit misbehaviour")
//             }
//         }
//     }
// }
