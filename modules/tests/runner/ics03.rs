use std::array::IntoIter;
use std::collections::HashMap;
use std::fmt::Debug;
use std::iter::FromIterator;

use ibc::ics03_connection::error::Kind as ICS03ErrorKind;
use ibc::ics03_connection::{
    connection::State as ConnectionState,
    msgs::{
        conn_open_ack::MsgConnectionOpenAck, conn_open_confirm::MsgConnectionOpenConfirm,
        conn_open_init::MsgConnectionOpenInit, conn_open_try::MsgConnectionOpenTry, ConnectionMsg,
    },
};

use ibc::ics03_connection::context::ConnectionReader;
use ibc::ics18_relayer::error::Error as ICS18Error;
use ibc::ics26_routing::msgs::Ics26Envelope;
use ibc::mock::context::MockContext;
use ibc::mock::host::HostType;
use serde::{Deserialize, Deserializer, Serialize};

use modelator::{event::Runner, tester::TestResult, ActionHandler, StateHandler};

use crate::{chain_action};

use super::ibcsystem::IBCSystem;

#[derive(Debug, Clone, Deserialize, PartialEq)]
pub struct AbstractState {
    pub chains: HashMap<String, Chain>,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
pub struct Chain {
    pub height: u64,
    pub connections: HashMap<u64, Connection>,
}

impl Chain {
    pub fn new(height: u64) -> Chain {
        Chain {
            height,
            connections: HashMap::new(),
        }
    }
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

impl StateHandler<AbstractState> for IBCSystem {
    fn init(&mut self, state: AbstractState) {
        // initiliaze all chains
        self.contexts.clear();
        for (chain_id, chain) in state.chains {
            // never GC blocks
            let max_history_size = usize::MAX;
            let ctx = MockContext::new(
                self.make(chain_id.clone()),
                HostType::Mock,
                max_history_size,
                self.make(chain.height),
            );
            assert!(self.contexts.insert(chain_id, ctx).is_none());
        }
    }

    fn read(&self) -> AbstractState {
        let mut chains = HashMap::new();
        for (chain_id, ctx) in &self.contexts {
            let mut connections = HashMap::new();
            let ctr = ConnectionReader::connection_counter(ctx);
            for connection_id in 0..ctr {
                if let Some(connection_end) = ctx.connection_end(&self.make(connection_id)) {
                    let connection = Connection {
                        client_id: Some(self.make(connection_end.client_id().clone())),
                        connection_id: Some(connection_id),
                        counterparty_client_id: Some(self
                            .make(connection_end.counterparty().client_id().clone())),
                        counterparty_connection_id: connection_end
                            .counterparty()
                            .connection_id()
                            .map(|id| self.make(id.clone())),
                        state: connection_end.state().clone(),
                    };
                    connections.insert(connection_id, connection);
                }
            }
            chains.insert(
                chain_id.clone(),
                Chain {
                    height: ctx.host_current_height().revision_height,
                    connections,
                },
            );
        }
        AbstractState { chains }
    }
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
pub struct ChainAction {
    pub chain_id: String,
    #[serde(flatten)]
    pub action: Action,
}

chain_action! { connection_open_init: ICS03ConnectionOpenInit
    client_id: u64,
    counterparty_chain_id: String,
    counterparty_client_id: u64
}

chain_action! { connection_open_try: ICS03ConnectionOpenTry
    [serde(default, deserialize_with = "deserialize_id")]
    previous_connection_id: Option<u64>,
    client_id: u64,
    client_state: u64,
    counterparty_chain_id: String,
    counterparty_client_id: u64,
    counterparty_connection_id: u64
}
chain_action! { connection_open_ack: ICS03ConnectionOpenAck
    connection_id: u64,
    client_state: u64,
    counterparty_chain_id: String,
    counterparty_connection_id: u64
}
chain_action! { connection_open_confirm: ICS03ConnectionOpenConfirm
    connection_id: u64,
    client_state: u64,
    counterparty_chain_id: String,
    counterparty_connection_id: u64
}     

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(tag = "type")]
pub enum Action {
    ICS03ConnectionOpenInit(ICS03ConnectionOpenInit),
    ICS03ConnectionOpenTry(ICS03ConnectionOpenTry),
    ICS03ConnectionOpenAck(ICS03ConnectionOpenAck),
    ICS03ConnectionOpenConfirm(ICS03ConnectionOpenConfirm),
}

#[derive(Debug, Clone, PartialEq, Deserialize, Serialize)]
pub enum ActionOutcome {
    OK,
    ICS03MissingClient,
    ICS03InvalidConsensusHeight,
    ICS03ConnectionNotFound,
    ICS03ConnectionMismatch,
    ICS03MissingClientConsensusState,
    ICS03InvalidProof,
    ICS03UninitializedConnection,
}

impl IBCSystem {
    fn encode_connection_action(&self, action: Action) -> ConnectionMsg {
        match action {
            Action::ICS03ConnectionOpenInit(action) => {
                ConnectionMsg::ConnectionOpenInit(MsgConnectionOpenInit {
                    client_id: self.make(action.client_id),
                    counterparty: self.make((action.counterparty_client_id, None as Option<u64>)),
                    version: self.take(),
                    delay_period: self.take_as("delay_period"),
                    signer: self.take(),
                })
            }
            Action::ICS03ConnectionOpenTry(action) => {
                ConnectionMsg::ConnectionOpenTry(Box::new(MsgConnectionOpenTry {
                    previous_connection_id: action.previous_connection_id.map(|x| self.make(x)),
                    client_id: self.make(action.client_id),
                    // TODO: is this ever needed?
                    client_state: None,
                    counterparty: self.make((
                        action.counterparty_client_id,
                        Some(action.counterparty_connection_id),
                    )),
                    counterparty_versions: self.take(),
                    proofs: self.make(action.client_state),
                    delay_period: self.take_as("delay_period"),
                    signer: self.take(),
                }))
            }
            Action::ICS03ConnectionOpenAck(action) => {
                ConnectionMsg::ConnectionOpenAck(Box::new(MsgConnectionOpenAck {
                    connection_id: self.make(action.connection_id),
                    counterparty_connection_id: self.make(action.counterparty_connection_id),
                    // TODO: is this ever needed?
                    client_state: None,
                    proofs: self.make(action.client_state),
                    version: self.take(),
                    signer: self.take(),
                }))
            }
            Action::ICS03ConnectionOpenConfirm(action) => {
                ConnectionMsg::ConnectionOpenConfirm(MsgConnectionOpenConfirm {
                    connection_id: self.make(action.connection_id),
                    proofs: self.make(action.client_state),
                    signer: self.take(),
                })
            }
        }
    }

    fn decode_connection_outcome(&self, ics18_result: Result<(), ICS18Error>) -> ActionOutcome {
        if ics18_result.is_ok() {
            ActionOutcome::OK
        } else if let Some(kind) = Self::extract_handler_error::<ICS03ErrorKind>(&ics18_result) {
            match kind {
                ICS03ErrorKind::MissingClient(_) => ActionOutcome::ICS03MissingClient,
                ICS03ErrorKind::InvalidConsensusHeight(_, _) => ActionOutcome::ICS03InvalidConsensusHeight,
                ICS03ErrorKind::ConnectionNotFound(_) => ActionOutcome::ICS03ConnectionNotFound,
                ICS03ErrorKind::ConnectionMismatch(_) => ActionOutcome::ICS03ConnectionMismatch,
                ICS03ErrorKind::MissingClientConsensusState(_, _) => ActionOutcome::ICS03MissingClientConsensusState,
                ICS03ErrorKind::InvalidProof => ActionOutcome::ICS03InvalidProof,
                ICS03ErrorKind::UninitializedConnection(_) => ActionOutcome::ICS03UninitializedConnection,
                _ => panic!("unexpected ICS03ErrorKind"),
            }
        } else {
            panic!("unexpected error")
        }
    }
}

impl ActionHandler<ChainAction> for IBCSystem {
    type Outcome = ActionOutcome;

    fn handle(&mut self, action: ChainAction) -> Self::Outcome {
        let msg = self.encode_connection_action(action.action.clone());
        let ctx = self.chain_context_mut(&action.chain_id);
        let result = ctx.deliver(Ics26Envelope::Ics3Msg(msg));
        self.decode_connection_outcome(result)
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use super::super::ics02::{AbstractState as ClientState, ChainAction as ClientAction};

    #[test]
    pub fn test() {
        let initial = AbstractState {
            chains: HashMap::from_iter(IntoIter::new([
                ("chain1".into(), Chain::new(10)),
                ("chain2".into(), Chain::new(20)),
            ])),
        };

        let events = modelator::EventStream::new()
            // initialize the state of your system from abstract state
            .init(initial)
            // you can inspect the current abstract state of your system
            .check(|state: AbstractState| println!("{:?}", state))
            // or make assertions about it
            .check(|state: AbstractState| assert_eq!(state.chains.len(), 2))
            // you can also execute abstract actions against your system
            .action(ChainAction::connection_open_init("chain1", 10, "chain2".to_string(), 30))
            // should fail because no client exist yet
            .outcome(ActionOutcome::ICS03MissingClient)
            // let's create the client
            .action(ClientAction::create_client("chain1", 10, 20))
            // and try again
            .action(ChainAction::connection_open_init("chain1", 0, "chain2".to_string(), 30))
            // should pass now
            .outcome(ActionOutcome::OK)
            // debug-print the client state
            .check(|state: ClientState| println!("{:?}", state))
            // debug-print the connection state
            .check(|state: AbstractState| println!("{:?}", state))
            ;

        let mut runner = Runner::<IBCSystem>::new()
            .with_state::<AbstractState>()
            .with_action::<ChainAction>()
            .with_state::<ClientState>()
            .with_action::<ClientAction>()
            ;
        let mut system = IBCSystem::new();
        let result = runner.run(&mut system, &mut events.into_iter());
        assert!(matches!(result, TestResult::Success(_)))
    }
}
