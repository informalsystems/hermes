use std::fmt::Debug;
use std::collections::HashMap;
use std::iter::FromIterator;
use std::array::IntoIter;

use ibc::{ics03_connection::context::ConnectionReader};
use ibc::ics02_client::context::ClientReader;
use ibc::ics02_client::msgs::create_client::MsgCreateAnyClient;
use ibc::ics02_client::msgs::update_client::MsgUpdateAnyClient;
use ibc::ics02_client::msgs::ClientMsg;
use ibc::ics26_routing::msgs::Ics26Envelope;
use serde::{Deserialize, Serialize};
use ibc::ics02_client::error::Kind as ICS02ErrorKind;
use ibc::ics18_relayer::error::Error as ICS18Error;

use modelator::{ActionHandler, StateHandler, event::Runner, tester::TestResult};

use super::ibcsystem::IBCSystem;

#[derive(Debug, Clone, Deserialize, PartialEq)]
pub struct ClientsState {
    pub chains: HashMap<String, Chain>,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
pub struct Chain {
    pub height: u64,
    pub clients: HashMap<u64, Client>,
}

impl Chain {
    pub fn new(height: u64) -> Chain {
        Chain {
            height,
            clients: HashMap::new()
        }
    }
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
pub struct Client {
    pub heights: Vec<u64>,
}

impl StateHandler<ClientsState> for IBCSystem {
    fn init(&mut self, state: ClientsState) {
        self.init(state.chains.iter().map(|(chain_id, chain)|(chain_id.clone(), chain.height)));
    }

    fn read(&self) -> ClientsState {
        let mut chains = HashMap::new();
        for (chain_id, ctx) in &self.contexts {
            let mut clients = HashMap::new();
            let ctr = ClientReader::client_counter(ctx);
            for client_id in 0..ctr {
                if let Some(states) = ctx.consensus_states(&self.make(client_id)) {
                    let mut heights: Vec<u64> = states.keys().into_iter().map(|h|h.revision_height).collect();
                    heights.sort();
                    clients.insert(client_id, Client { heights });
                }
            }
            chains.insert(chain_id.clone(), Chain { 
                height: ctx.host_current_height().revision_height,
                clients
            });
        }
        ClientsState {
            chains
        }
    }
}

#[derive(Debug, Clone, PartialEq, Deserialize, Serialize)]
pub struct ChainClientAction {
    pub chain_id: String,
    #[serde(flatten)]
    pub client_action: ClientAction,
}

impl ChainClientAction {
    pub fn create_client(chain_id: &str, client_state: u64, consensus_state: u64) -> ChainClientAction {
        ChainClientAction {
            chain_id: chain_id.to_string(),
            client_action: ClientAction::ICS02CreateClient(
                ICS02CreateClient { client_state, consensus_state }
            ),
        }
    }
    pub fn update_client(chain_id: &str, client_id: u64, header: u64) -> ChainClientAction {
        ChainClientAction {
            chain_id: chain_id.to_string(),
            client_action: ClientAction::ICS02UpdateClient(
                ICS02UpdateClient { client_id, header }
            ),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Deserialize, Serialize)]
#[serde(tag = "type")]
pub enum ClientAction {
    ICS02CreateClient(ICS02CreateClient),
    ICS02UpdateClient(ICS02UpdateClient),
}

#[derive(Debug, Clone, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ICS02CreateClient {
    pub client_state: u64,
    pub consensus_state: u64,
}

#[derive(Debug, Clone, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ICS02UpdateClient {
    pub client_id: u64,
    pub header: u64,
}

#[derive(Debug, Clone, PartialEq, Deserialize, Serialize)]
pub enum ClientActionOutcome {
    OK,
    ICS02ClientNotFound,
    ICS02HeaderVerificationFailure,
}


impl IBCSystem {
    fn encode_client_action(&self, action: ClientAction) -> ClientMsg {
        match action {
            ClientAction::ICS02CreateClient(action) => 
                ClientMsg::CreateClient(MsgCreateAnyClient {
                    client_state: self.make(action.client_state),
                    consensus_state: self.make(action.consensus_state),
                    signer: self.take(),
                }),
            ClientAction::ICS02UpdateClient(action) => 
                ClientMsg::UpdateClient(MsgUpdateAnyClient {
                    client_id: self.make(action.client_id),
                    header: self.make(action.header),
                    signer: self.take(),
                })
        }
    }

    fn decode_client_outcome(&self, ics18_result: Result<(), ICS18Error>) -> ClientActionOutcome {
            if ics18_result.is_ok() {
                ClientActionOutcome::OK
            }
            else if let Some(kind) = Self::extract_handler_error::<ICS02ErrorKind>(&ics18_result) {
                match kind {
                    ICS02ErrorKind::ClientNotFound(_) => ClientActionOutcome::ICS02ClientNotFound,
                    ICS02ErrorKind::HeaderVerificationFailure => ClientActionOutcome::ICS02HeaderVerificationFailure,
                    _ => panic!("unexpected ICS02ErrorKind"),
                }
            }
            else {
                panic!("unexpected error")
            }

    }
}   

impl ActionHandler<ChainClientAction> for IBCSystem {
    type Outcome = ClientActionOutcome;

    fn handle(&mut self, action: ChainClientAction) -> Self::Outcome {
        let msg = Ics26Envelope::Ics2Msg(self.encode_client_action(action.client_action.clone()));
        let ctx = self.chain_context_mut(&action.chain_id);
        let result = ctx.deliver(msg);
        self.decode_client_outcome(result)
    }
}

#[test]
pub fn test() {
    let mut runner = Runner::<IBCSystem>::new()
        .with_state::<ClientsState>()
        .with_action::<ChainClientAction>();

        let initial = ClientsState {
            chains: HashMap::from_iter(IntoIter::new([
                ("chain1".into(), Chain::new(10)),
                ("chain2".into(), Chain::new(20))
             ]))
        };

        let events = modelator::event::EventStream::new()
            // initialize the state of your system from abstract state
            .init(initial)
            // you can inspect the current abstract state of your system
            .check(|state: ClientsState| println!("{:?}", state) )
            // or make assertions about it
            .check(|state: ClientsState| assert_eq!(state.chains.len(), 2) )
            // you can also execute abstract actions against your system
            .action(ChainClientAction::create_client("chain1", 10, 20))
            // and require a particular outcome of the action
            .outcome(ClientActionOutcome::OK)
            .check(|state: ClientsState| assert_eq!(state.chains["chain1"].clients.len(), 1))
            .action(ChainClientAction::update_client("chain1", 1, 30))
            // there is no client with id 1
            .outcome(ClientActionOutcome::ICS02ClientNotFound)
            .action(ChainClientAction::update_client("chain1", 0, 30))
            // debug-print the state again
            .check(|state: ClientsState| println!("{:?}", state) )
            .check(|state: ClientsState| assert_eq!(state.chains["chain1"].clients[&0].heights, vec![10,30]) );

        let mut system = IBCSystem::new();
        let result = runner.run(&mut system, &mut events.into_iter());
        assert!(matches!(result, TestResult::Success(_)))
}
