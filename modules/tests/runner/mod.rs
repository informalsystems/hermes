pub mod step;

use std::error::Error;
use std::fmt::{Debug, Display};
use std::{any::Any, collections::HashMap};

use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
use ibc::ics02_client::client_type::ClientType;
use ibc::ics02_client::context::ClientReader;
use ibc::ics02_client::error::Kind as ICS02ErrorKind;
use ibc::ics02_client::msgs::create_client::MsgCreateAnyClient;
use ibc::ics02_client::msgs::update_client::MsgUpdateAnyClient;
use ibc::ics02_client::msgs::ClientMsg;
use ibc::ics03_connection::connection::{Counterparty, State as ConnectionState};
use ibc::ics03_connection::error::Kind as ICS03ErrorKind;
use ibc::ics03_connection::msgs::conn_open_ack::MsgConnectionOpenAck;
use ibc::ics03_connection::msgs::conn_open_confirm::MsgConnectionOpenConfirm;
use ibc::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
use ibc::ics03_connection::msgs::conn_open_try::MsgConnectionOpenTry;
use ibc::ics03_connection::msgs::ConnectionMsg;
use ibc::ics03_connection::version::Version;
use ibc::ics04_channel::context::ChannelReader;
use ibc::ics18_relayer::context::Ics18Context;
use ibc::ics18_relayer::error::{Error as ICS18Error, Kind as ICS18ErrorKind};
use ibc::ics23_commitment::commitment::{CommitmentPrefix, CommitmentProofBytes};
use ibc::ics24_host::identifier::{ChainId, ClientId, ConnectionId};
use ibc::ics26_routing::error::{Error as ICS26Error, Kind as ICS26ErrorKind};
use ibc::ics26_routing::msgs::Ics26Envelope;
use ibc::mock::client_state::{MockClientState, MockConsensusState};
use ibc::mock::context::MockContext;
use ibc::mock::header::MockHeader;
use ibc::mock::host::HostType;
use ibc::proofs::{ConsensusProof, Proofs};
use ibc::signer::Signer;
use ibc::Height;

use modelator::Converter;
use step::{
    Action, ActionOutcome, Chain, ClientAction, ConnectionAction, ICS02CreateClient,
    ICS02UpdateClient, ICS03ConnectionOpenAck, ICS03ConnectionOpenConfirm, ICS03ConnectionOpenInit,
    ICS03ConnectionOpenTry, Step,
};

#[derive(Debug)]
pub struct IBCTestRunner {
    // mapping from chain identifier to its context
    contexts: HashMap<ChainId, MockContext>,
    converter: Converter,
}

impl IBCTestRunner {
    pub fn new() -> Self {
        Self {
            contexts: Default::default(),
            converter: Self::make_converter(),
        }
    }

    pub fn make_converter() -> Converter {
        let mut c = Converter::new();
        c.add(|c, chain_id: String| ChainId::new(chain_id, c.default_as("revision")));
        c.def_as("revision", |_| 0u64);
        c.def(|_| Version::default());
        c.def::<Vec<Version>>(|c| vec![c.default()]);
        c.add(|_, client_id: u64| {
            ClientId::new(ClientType::Mock, client_id)
                .expect("it should be possible to create the client identifier")
        });
        c.add(|_, connection_id: u64| ConnectionId::new(connection_id));

        c.add(|_, height: u64| Height::new(0, height));
        c.add(|c, height: u64| MockHeader::new(c.convert(height)));
        c.add(|c, height: u64| AnyHeader::Mock(c.convert(height)));
        c.add(|c, height: u64| AnyClientState::Mock(MockClientState(c.convert(height))));
        c.add(|c, height: u64| AnyConsensusState::Mock(MockConsensusState(c.convert(height))));
        c.def(|_| Signer::new(""));
        c.add(|c, (client_id, connection_id): (u64, Option<u64>)| {
            Counterparty::new(
                c.convert(client_id),
                connection_id.map(|id| c.convert(id)),
                c.default(),
            )
        });
        c.def_as("delay_period", |_| 0u64);
        c.def::<CommitmentPrefix>(|_| vec![0].into());
        c.def::<CommitmentProofBytes>(|_| vec![0].into());
        c.add(|c, height: u64| {
            ConsensusProof::new(c.default(), c.convert(height))
                .expect("it should be possible to create the consensus proof")
        });
        c.add(|c, height: u64| {
            Proofs::new(
                c.default(),
                None,
                Some(c.convert(height)),
                None,
                c.convert(height),
            )
            .expect("it should be possible to create the proofs")
        });
        c.add(|c, action: ICS02CreateClient| {
            ClientMsg::CreateClient(MsgCreateAnyClient {
                client_state: c.convert(action.client_state),
                consensus_state: c.convert(action.consensus_state),
                signer: c.default(),
            })
        });
        c.add(|c, action: ICS02UpdateClient| {
            ClientMsg::UpdateClient(MsgUpdateAnyClient {
                client_id: c.convert(action.client_id),
                header: c.convert(action.header),
                signer: c.default(),
            })
        });
        c.add(|c, action: ClientAction| {
            Ics26Envelope::Ics2Msg(match action {
                ClientAction::None => panic!("unexpected action type"),
                ClientAction::ICS02CreateClient(a) => c.convert(a),
                ClientAction::ICS02UpdateClient(a) => c.convert(a),
            })
        });
        c.add(|c, action: ICS03ConnectionOpenInit| {
            ConnectionMsg::ConnectionOpenInit(MsgConnectionOpenInit {
                client_id: c.convert(action.client_id),
                counterparty: c.convert((action.counterparty_client_id, None as Option<u64>)),
                version: c.default(),
                delay_period: c.default_as("delay_period"),
                signer: c.default(),
            })
        });
        c.add(|c, action: ICS03ConnectionOpenTry| {
            ConnectionMsg::ConnectionOpenTry(Box::new(
                MsgConnectionOpenTry {
                    previous_connection_id: action.previous_connection_id.map(|x| c.convert(x)),
                    client_id: c.convert(action.client_id),
                    // TODO: is this ever needed?
                    client_state: None,
                    counterparty: c.convert((
                        action.counterparty_client_id,
                        Some(action.counterparty_connection_id),
                    )),
                    counterparty_versions: c.default(),
                    proofs: c.convert(action.client_state),
                    delay_period: c.default_as("delay_period"),
                    signer: c.default(),
                },
            ))
        });
        c.add(|c, action: ICS03ConnectionOpenAck| {
            ConnectionMsg::ConnectionOpenAck(Box::new(
                MsgConnectionOpenAck {
                    connection_id: c.convert(action.connection_id),
                    counterparty_connection_id: c.convert(action.counterparty_connection_id),
                    // TODO: is this ever needed?
                    client_state: None,
                    proofs: c.convert(action.client_state),
                    version: c.default(),
                    signer: c.default(),
                },
            ))
        });
        c.add(|c, action: ICS03ConnectionOpenConfirm| {
            ConnectionMsg::ConnectionOpenConfirm(
                MsgConnectionOpenConfirm {
                    connection_id: c.convert(action.connection_id),
                    proofs: c.convert(action.client_state),
                    signer: c.default(),
                },
            )
        });
        c.add(|c, action: ConnectionAction| {
            Ics26Envelope::Ics3Msg(match action {
                ConnectionAction::None => panic!("unexpected action type"),
                ConnectionAction::ICS03ConnectionOpenInit(a) => c.convert(a),
                ConnectionAction::ICS03ConnectionOpenTry(a) => c.convert(a),
                ConnectionAction::ICS03ConnectionOpenAck(a) => c.convert(a),
                ConnectionAction::ICS03ConnectionOpenConfirm(a) => c.convert(a),
            })
        });
        c.add(|_, error: ICS02ErrorKind|
            match error {
                ICS02ErrorKind::ClientNotFound(_) => ActionOutcome::ICS02ClientNotFound,
                ICS02ErrorKind::HeaderVerificationFailure => ActionOutcome::ICS02HeaderVerificationFailure,
                _ => panic!("unexpected ICS02ErrorKind"),
            }
        );        
        c.add(|_, error: ICS03ErrorKind|
            match error {
                ICS03ErrorKind::MissingClient(_) => ActionOutcome::ICS03MissingClient,
                ICS03ErrorKind::InvalidConsensusHeight(_,_) => ActionOutcome::ICS03InvalidConsensusHeight,
                ICS03ErrorKind::ConnectionNotFound(_) => ActionOutcome::ICS03ConnectionNotFound,
                ICS03ErrorKind::ConnectionMismatch(_) => ActionOutcome::ICS03ConnectionMismatch,
                ICS03ErrorKind::MissingClientConsensusState(_,_) => ActionOutcome::ICS03MissingClientConsensusState,
                ICS03ErrorKind::InvalidProof => ActionOutcome::ICS03InvalidProof,
                ICS03ErrorKind::UninitializedConnection(_) => ActionOutcome::ICS03UninitializedConnection,
                _ => panic!("unexpected ICS03ErrorKind"),
            }
        );        
        c.add(|c, ics18_result: Result<(), ICS18Error>|
            if ics18_result.is_ok() {
                ActionOutcome::OK
            }
            else if let Some(kind) = Self::extract_handler_error::<ICS02ErrorKind>(&ics18_result) {
                c.convert(kind)
            }
            else if let Some(kind) = Self::extract_handler_error::<ICS03ErrorKind>(&ics18_result) {
                c.convert(kind)
            }
            else {
                panic!("unexpected error")
            }
        );        
        c
    }

     pub fn convert<From: Sized + Any, To: Sized + Any>(&self, from: From) -> To {
        self.converter.convert(from)
    }

    /// Create a `MockContext` for a given `chain_id`.
    /// Panic if a context for `chain_id` already exists.
    pub fn init_chain_context(&mut self, chain_id: String, initial_height: u64) {
        let chain_id: ChainId = self.convert(chain_id);
        // never GC blocks
        let max_history_size = usize::MAX;
        let ctx = MockContext::new(
            chain_id.clone(),
            HostType::Mock,
            max_history_size,
            Height::new(Self::revision(), initial_height),
        );
        assert!(self.contexts.insert(chain_id, ctx).is_none());
    }

    /// Returns a reference to the `MockContext` of a given `chain_id`.
    /// Panic if the context for `chain_id` is not found.
    pub fn chain_context(&self, chain_id: String) -> &MockContext {
        self.contexts
            .get(&self.convert(chain_id))
            .expect("chain context should have been initialized")
    }

    /// Returns a mutable reference to the `MockContext` of a given `chain_id`.
    /// Panic if the context for `chain_id` is not found.
    pub fn chain_context_mut(&mut self, chain_id: &str) -> &mut MockContext {
        self.contexts
            .get_mut(&self.convert(chain_id.to_string()))
            .expect("chain context should have been initialized")
    }

    pub fn extract_handler_error<K>(ics18_result: &Result<(), ICS18Error>) -> Option<K>
    where
        K: Clone + Debug + Display + Into<anomaly::BoxError> + 'static,
    {
        let ics18_error = ics18_result.as_ref().expect_err("ICS18 error expected");
        assert!(matches!(
            ics18_error.kind(),
            ICS18ErrorKind::TransactionFailed
        ));
        let ics26_error = ics18_error
            .source()
            .expect("expected source in ICS18 error")
            .downcast_ref::<ICS26Error>()
            .expect("ICS18 source should be an ICS26 error");
        assert!(matches!(
            ics26_error.kind(),
            ICS26ErrorKind::HandlerRaisedError,
        ));
        ics26_error
            .source()
            .expect("expected source in ICS26 error")
            .downcast_ref::<anomaly::Error<K>>()
            .map(|e| e.kind().clone())
    } 

    pub fn revision() -> u64 {
        0
    }

    pub fn client_id(client_id: u64) -> ClientId {
        ClientId::new(ClientType::Mock, client_id)
            .expect("it should be possible to create the client identifier")
    }

    pub fn connection_id(connection_id: u64) -> ConnectionId {
        ConnectionId::new(connection_id)
    }

    pub fn height(height: u64) -> Height {
        Height::new(Self::revision(), height)
    }

    /// Check that chain heights match the ones in the model.
    pub fn validate_chains(&self) -> bool {
        self.contexts.values().all(|ctx| ctx.validate().is_ok())
    }

    /// Check that chain states match the ones in the model.
    pub fn check_chain_states(&self, chains: HashMap<String, Chain>) -> bool {
        chains.into_iter().all(|(chain_id, chain)| {
            let ctx = self.chain_context(chain_id);
            // check that heights match
            let heights_match = ctx.query_latest_height() == Self::height(chain.height);

            // check that clients match
            let clients_match = chain.clients.into_iter().all(|(client_id, client)| {
                // compute the highest consensus state in the model and check
                // that it matches the client state
                let client_state = ClientReader::client_state(ctx, &Self::client_id(client_id));
                let client_state_matches = match client.heights.iter().max() {
                    Some(max_height) => {
                        // if the model has consensus states (encoded simply as
                        // heights in the model), then the highest one should
                        // match the height in the client state
                        client_state.is_some()
                            && client_state.unwrap().latest_height() == Self::height(*max_height)
                    }
                    None => {
                        // if the model doesn't have any consensus states
                        // (heights), then the client state should not exist
                        client_state.is_none()
                    }
                };

                // check that each consensus state from the model exists
                // TODO: check that no other consensus state exists (i.e. the
                //       only existing consensus states are those in that also
                //       exist in the model)
                let consensus_states_match = client.heights.into_iter().all(|height| {
                    ctx.consensus_state(&Self::client_id(client_id), Self::height(height))
                        .is_some()
                });

                client_state_matches && consensus_states_match
            });

            // check that connections match
            let connections_match =
                chain
                    .connections
                    .into_iter()
                    .all(|(connection_id, connection)| {
                        if connection.state == ConnectionState::Uninitialized {
                            // if the connection has not yet been initialized, then
                            // there's nothing to check
                            true
                        } else if let Some(connection_end) =
                            ctx.connection_end(&Self::connection_id(connection_id))
                        {
                            // states must match
                            let states_match = *connection_end.state() == connection.state;

                            // client ids must match
                            let client_ids = *connection_end.client_id()
                                == Self::client_id(connection.client_id.unwrap());

                            // counterparty client ids must match
                            let counterparty_client_ids =
                                *connection_end.counterparty().client_id()
                                    == Self::client_id(connection.counterparty_client_id.unwrap());

                            // counterparty connection ids must match
                            let counterparty_connection_ids =
                                connection_end.counterparty().connection_id()
                                    == connection
                                        .counterparty_connection_id
                                        .map(Self::connection_id)
                                        .as_ref();

                            states_match
                                && client_ids
                                && counterparty_client_ids
                                && counterparty_connection_ids
                        } else {
                            // if the connection exists in the model, then it must
                            // also exist in the implementation; in this case it
                            // doesn't, so we fail the verification
                            false
                        }
                    });

            heights_match && clients_match && connections_match
        })
    }
}

impl modelator::runner::TestRunner<Step> for IBCTestRunner {
    fn initial_step(&mut self, step: Step) -> bool {
        assert_eq!(
            step.action,
            Action::ClientAction(ClientAction::None),
            "unexpected action type"
        );
        assert_eq!(
            step.action_outcome,
            ActionOutcome::None,
            "unexpected action outcome"
        );
        // initiliaze all chains
        self.contexts.clear();
        for (chain_id, chain) in step.chains {
            self.init_chain_context(chain_id, chain.height);
        }
        true
    }

    fn next_step(&mut self, step: Step) -> bool {
        let msg = match &step.action {
            Action::ClientAction(action) => self.convert(action.clone()),
            Action::ConnectionAction(action) => self.convert(action.clone()),
        };
        let ctx = self.chain_context_mut(&step.chain_id);
        let result = ctx.deliver(msg);
        let outcome: ActionOutcome = self.convert(result);
        let outcome_matches = outcome == step.action_outcome;
  
        // also check the state of chains
        outcome_matches && self.validate_chains() && self.check_chain_states(step.chains)
    }
}
