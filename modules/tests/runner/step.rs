use ibc::ics03_connection::connection::State as ConnectionState;
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

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(tag = "type")]
pub enum Action {
    None,
    ICS02CreateClient {
        #[serde(alias = "chainId")]
        chain_id: String,

        #[serde(alias = "clientState")]
        client_state: u64,

        #[serde(alias = "consensusState")]
        consensus_state: u64,
    },
    ICS02UpdateClient {
        #[serde(alias = "chainId")]
        chain_id: String,

        #[serde(alias = "clientId")]
        client_id: u64,

        header: u64,
    },
    ICS03ConnectionOpenInit {
        #[serde(alias = "chainId")]
        chain_id: String,

        #[serde(alias = "clientId")]
        client_id: u64,

        #[serde(alias = "counterpartyChainId")]
        counterparty_chain_id: String,

        #[serde(alias = "counterpartyClientId")]
        counterparty_client_id: u64,
    },
    ICS03ConnectionOpenTry {
        #[serde(alias = "chainId")]
        chain_id: String,

        #[serde(alias = "previousConnectionId")]
        #[serde(default, deserialize_with = "deserialize_id")]
        previous_connection_id: Option<u64>,

        #[serde(alias = "clientId")]
        client_id: u64,

        #[serde(alias = "clientState")]
        client_state: u64,

        #[serde(alias = "counterpartyChainId")]
        counterparty_chain_id: String,

        #[serde(alias = "counterpartyClientId")]
        counterparty_client_id: u64,

        #[serde(alias = "counterpartyConnectionId")]
        counterparty_connection_id: u64,
    },
    ICS03ConnectionOpenAck {
        #[serde(alias = "chainId")]
        chain_id: String,

        #[serde(alias = "connectionId")]
        connection_id: u64,

        #[serde(alias = "clientState")]
        client_state: u64,

        #[serde(alias = "counterpartyChainId")]
        counterparty_chain_id: String,

        #[serde(alias = "counterpartyConnectionId")]
        counterparty_connection_id: u64,
    },
    ICS03ConnectionOpenConfirm {
        #[serde(alias = "chainId")]
        chain_id: String,

        #[serde(alias = "connectionId")]
        connection_id: u64,

        #[serde(alias = "clientState")]
        client_state: u64,

        #[serde(alias = "counterpartyChainId")]
        counterparty_chain_id: String,

        #[serde(alias = "counterpartyConnectionId")]
        counterparty_connection_id: u64,
    },
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
    ICS03ConnectionOpenTryOK,
    ICS03InvalidConsensusHeight,
    ICS03ConnectionNotFound,
    ICS03ConnectionMismatch,
    ICS03MissingClientConsensusState,
    ICS03InvalidProof,
    ICS03ConnectionOpenAckOK,
    ICS03UninitializedConnection,
    ICS03ConnectionOpenConfirmOK,
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
pub struct Connection {
    #[serde(alias = "clientId")]
    #[serde(default, deserialize_with = "deserialize_id")]
    pub client_id: Option<u64>,

    #[serde(alias = "connectionId")]
    #[serde(default, deserialize_with = "deserialize_id")]
    pub connection_id: Option<u64>,

    #[serde(alias = "counterpartyClientId")]
    #[serde(default, deserialize_with = "deserialize_id")]
    pub counterparty_client_id: Option<u64>,

    #[serde(alias = "counterpartyConnectionId")]
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
