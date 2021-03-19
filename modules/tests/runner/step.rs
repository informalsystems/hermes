use ibc::ics03_connection::connection::State as ConnectionState;
use serde::{Deserialize, Deserializer};
use std::collections::HashMap;
use std::fmt::Debug;

#[derive(Debug, Clone, Deserialize)]
pub struct Step {
    #[serde(alias = "actionChainId")]
    pub chain_id: String,

    pub action: Action,

    #[serde(alias = "actionOutcome")]
    pub action_outcome: ActionOutcome,

    pub chains: HashMap<String, Chain>,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(untagged)]
pub enum Action {
    ClientAction(ClientAction),
    ConnectionAction(ConnectionAction),
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(tag = "type")]
pub enum ClientAction {
    None,
    ICS02CreateClient(ICS02CreateClient),
    ICS02UpdateClient(ICS02UpdateClient),
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(tag = "type")]
pub enum ConnectionAction {
    None,
    ICS03ConnectionOpenInit(ICS03ConnectionOpenInit),
    ICS03ConnectionOpenTry(ICS03ConnectionOpenTry),
    ICS03ConnectionOpenAck(ICS03ConnectionOpenAck),
    ICS03ConnectionOpenConfirm(ICS03ConnectionOpenConfirm),
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ICS02CreateClient {
    pub client_state: u64,
    pub consensus_state: u64,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ICS02UpdateClient {
    pub client_id: u64,
    pub header: u64,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ICS03ConnectionOpenInit {
    pub client_id: u64,
    pub counterparty_chain_id: String,
    pub counterparty_client_id: u64,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ICS03ConnectionOpenTry {
    #[serde(default, deserialize_with = "deserialize_id")]
    pub previous_connection_id: Option<u64>,
    pub client_id: u64,
    pub client_state: u64,
    pub counterparty_chain_id: String,
    pub counterparty_client_id: u64,
    pub counterparty_connection_id: u64,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ICS03ConnectionOpenAck {
    pub connection_id: u64,
    pub client_state: u64,
    pub counterparty_chain_id: String,
    pub counterparty_connection_id: u64,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ICS03ConnectionOpenConfirm {
    pub connection_id: u64,
    pub client_state: u64,
    pub counterparty_chain_id: String,
    pub counterparty_connection_id: u64,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
pub enum ActionOutcome {
    None,
    OK,
    ICS02ClientNotFound,
    ICS02HeaderVerificationFailure,
    ICS03MissingClient,
    ICS03InvalidConsensusHeight,
    ICS03ConnectionNotFound,
    ICS03ConnectionMismatch,
    ICS03MissingClientConsensusState,
    ICS03InvalidProof,
    ICS03UninitializedConnection,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
pub struct Chain {
    pub height: u64,

    pub clients: HashMap<u64, Client>,

    pub connections: HashMap<u64, Connection>,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
pub struct Client {
    pub heights: Vec<u64>,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Connection {
    #[serde(default, deserialize_with = "deserialize_id")]
    pub client_id: Option<u64>,

    #[serde(default, deserialize_with = "deserialize_id")]
    pub connection_id: Option<u64>,

    #[serde(default, deserialize_with = "deserialize_id")]
    pub counterparty_client_id: Option<u64>,

    #[serde(default, deserialize_with = "deserialize_id")]
    pub counterparty_connection_id: Option<u64>,

    pub state: ConnectionState,
}

/// On the model, a non-existing `client_id` and a `connection_id` is
/// represented with -1.
/// For this reason, this function maps a `Some(-1)` to a `None`.
fn deserialize_id<'de, D>(deserializer: D) -> Result<Option<u64>, D::Error>
where
    D: Deserializer<'de>,
{
    let id: Option<i64> = Deserialize::deserialize(deserializer)?;
    let id = if id == Some(-1) {
        None
    } else {
        id.map(|id| id as u64)
    };
    Ok(id)
}
