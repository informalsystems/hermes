use serde::Deserialize;
use std::collections::HashMap;
use std::fmt::Debug;

#[derive(Debug, Clone, Deserialize)]
pub struct Step {
    pub action: Action,

    #[serde(alias = "actionOutcome")]
    pub action_outcome: ActionOutcome,

    pub chains: HashMap<String, Chain>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Action {
    #[serde(alias = "type")]
    pub action_type: ActionType,

    #[serde(alias = "chainId")]
    pub chain_id: Option<String>,

    #[serde(alias = "clientId")]
    pub client_id: Option<u64>,

    #[serde(alias = "clientHeight")]
    pub client_height: Option<u64>,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
pub enum ActionType {
    None,
    ICS02CreateClient,
    ICS02UpdateClient,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
pub enum ActionOutcome {
    None,
    ICS02CreateOK,
    ICS02UpdateOK,
    ICS02ClientNotFound,
    ICS02HeaderVerificationFailure,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
pub struct Chain {
    pub height: u64,
}
