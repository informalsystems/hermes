use std::fmt::Debug;
use std::collections::HashMap;

use ibc::{ics03_connection::context::ConnectionReader};
use ibc::ics02_client::context::ClientReader;
use ibc::ics02_client::msgs::create_client::MsgCreateAnyClient;
use ibc::ics02_client::msgs::update_client::MsgUpdateAnyClient;
use ibc::ics02_client::msgs::ClientMsg;
use ibc::ics26_routing::msgs::Ics26Envelope;
use ibc::mock::context::MockContext;
use ibc::mock::host::HostType;
use serde::{Deserialize, Serialize};
use ibc::ics02_client::error::Kind as ICS02ErrorKind;
use ibc::ics18_relayer::error::Error as ICS18Error;

use modelator::{StateHandler, ActionHandler};

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

#[derive(Debug, Clone, PartialEq, Deserialize)]
pub struct Client {
    pub heights: Vec<u64>,
}

impl StateHandler<ClientsState> for IBCSystem {
    fn init(&mut self, state: ClientsState) {
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

#[derive(Debug, Clone, PartialEq, Deserialize)]
pub enum ClientActionOutcome {
    OK,
    ICS02ClientNotFound,
    ICS02HeaderVerificationFailure,
}



#[test]
pub fn test() {
    let x = ICS02CreateClient {
        client_state: 10,
        consensus_state: 20,
        
    };
    let m = ChainClientAction {
        chain_id: "1".to_string(),
        client_action: ClientAction::ICS02CreateClient(x),

    };
    
    

    let s = serde_json::to_string_pretty(&m).unwrap();
    println!("{}", &s);

    let m2: ChainClientAction = serde_json::from_str(&s).unwrap();
    println!("{:?}", m2);
    

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
        let msg = self.encode_client_action(action.client_action.clone());
        let ctx = self.chain_context_mut(&action.chain_id);
        let result = ctx.deliver(Ics26Envelope::Ics2Msg(msg));
        self.decode_client_outcome(result)
    }
}

