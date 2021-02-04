use serde::{Deserialize, Deserializer};
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

    #[serde(alias = "counterpartyClientId")]
    pub counterparty_client_id: Option<u64>,

    #[serde(alias = "connectionId")]
    #[serde(default, deserialize_with = "deserialize_connection_id")]
    pub connection_id: Option<u64>,
}

/// On the model, a non-existing `connection_id` is represented with -1.
/// For this reason, this function maps a `Some(-1)` to a `None`.
fn deserialize_connection_id<'de, D>(deserializer: D) -> Result<Option<u64>, D::Error>
where
    D: Deserializer<'de>,
{
    let connection_id: Option<i64> = Deserialize::deserialize(deserializer)?;
    let connection_id = if connection_id == Some(-1) {
        None
    } else {
        connection_id.map(|connection_id| connection_id as u64)
    };
    Ok(connection_id)
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
pub enum ActionType {
    None,
    ICS02CreateClient,
    ICS02UpdateClient,
    ICS03ConnectionOpenInit,
    ICS03ConnectionOpenTry,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
pub enum ActionOutcome {
    None,
    ICS02CreateOK,
    ICS02UpdateOK,
    ICS02ClientNotFound,
    ICS02HeaderVerificationFailure,
    ICS03ConnectionOpenInitOK,
    ICS03MissingClient,
    ICS03InvalidConsensusHeight,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
pub struct Chain {
    pub height: u64,
}
