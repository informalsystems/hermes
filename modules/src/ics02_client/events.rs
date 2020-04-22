//! Types for the IBC events emitted from Tendermint Websocket for the client modules.

use tendermint::rpc::event_listener::Event;
use std::convert::TryFrom;
use serde_json::Value;


struct CreateClientEvent{
    data: Value
}

impl TryFrom<Event> for CreateClientEvent{
    type Error = &'static str;
    fn try_from(event: Event) -> Result<Self, Self::Error> { 
        match event {
            Event::GenericJSONEvent{ref data}=>{ 
                match data{
                    Value::Object(obj) => {
                        if obj["type"].as_str() == Some("create_client"){
                            return Ok(CreateClientEvent{data: data.clone()})
                        }
                    Err("Expected JSON representing a CreateClient, got wrong type")?
                    },
                   _ => {Err("Expected JSON representing a CreateClient, got wrong type")?}
                }
            },
            Event::GenericStringEvent{..} => Err("Generic event is not of type create client")
        }
    } 
}