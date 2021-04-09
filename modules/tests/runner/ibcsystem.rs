use std::error::Error;
use std::{any::Any, collections::HashMap};
use std::{
    fmt::{Debug, Display},
    slice::Iter,
};

use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
use ibc::ics02_client::client_type::ClientType;
use ibc::ics03_connection::connection::Counterparty;
use ibc::ics03_connection::version::Version;
use ibc::ics18_relayer::error::{Error as ICS18Error, Kind as ICS18ErrorKind};
use ibc::ics23_commitment::commitment::{CommitmentPrefix, CommitmentProofBytes};
use ibc::ics24_host::identifier::{ChainId, ClientId, ConnectionId};
use ibc::ics26_routing::error::{Error as ICS26Error, Kind as ICS26ErrorKind};
use ibc::mock::client_state::{MockClientState, MockConsensusState};
use ibc::mock::context::MockContext;
use ibc::mock::header::MockHeader;
use ibc::proofs::{ConsensusProof, Proofs};
use ibc::signer::Signer;
use ibc::Height;

use modelator::Recipe;

#[derive(Debug)]
pub struct IBCSystem {
    // mapping from abstract chain identifier to its context
    pub contexts: HashMap<String, MockContext>,
    pub recipe: Recipe,
}

impl IBCSystem {
    pub fn new() -> IBCSystem {
        IBCSystem {
            contexts: HashMap::new(),
            recipe: Self::make_recipe(),
        }
    }

    // Initialize the system for a set of chains with given ids and heights
    pub fn init(&mut self, chains: impl Iterator<Item = (String, u64)>) {
        self.contexts.clear();
        for (chain_id, height) in chains {
            let max_history_size = usize::MAX;
            let ctx = MockContext::new(
                self.make(chain_id.clone()),
                ibc::mock::host::HostType::Mock,
                max_history_size,
                self.make(height),
            );
            self.contexts.insert(chain_id, ctx);
        }
    }

    pub fn make<From: Sized + Any, To: Sized + Any>(&self, x: From) -> To {
        self.recipe.make(x)
    }

    pub fn take<T: Sized + Any>(&self) -> T {
        self.recipe.take()
    }

    pub fn take_as<T: Sized + Any>(&self, name: &str) -> T {
        self.recipe.take_as(name)
    }

    /// Returns a reference to the `MockContext` of a given `chain_id`.
    /// Panic if the context for `chain_id` is not found.
    pub fn chain_context(&self, chain_id: String) -> &MockContext {
        self.contexts
            .get(&chain_id)
            .expect("chain context should have been initialized")
    }

    /// Returns a mutable reference to the `MockContext` of a given `chain_id`.
    /// Panic if the context for `chain_id` is not found.
    pub fn chain_context_mut(&mut self, chain_id: &str) -> &mut MockContext {
        self.contexts
            .get_mut(chain_id)
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

    pub fn make_recipe() -> Recipe {
        let mut r = Recipe::new();
        r.add(|r, chain_id: String| ChainId::new(chain_id, r.take_as("revision")));
        r.put_as("revision", |_| 0u64);
        r.put(|_| Version::default());
        r.put::<Vec<Version>>(|r| vec![r.take()]);
        r.add(|_, client_id: u64| {
            ClientId::new(ClientType::Mock, client_id)
                .expect("it should be possible to create the client identifier")
        });
        r.add(|_, client_id: ClientId| {
            client_id
                .as_str()
                .split("-")
                .last()
                .expect("a valid ClientId should be separated by '-'")
                .parse::<u64>()
                .expect("a valid ClientId should have a numeric counter at the end")
        });
        r.add(|_, connection_id: u64| ConnectionId::new(connection_id));
        r.add(|_, connection_id: ConnectionId| {
            connection_id
                .as_str()
                .split("-")
                .last()
                .expect("a valid ConnectionId should be separated by '-'")
                .parse::<u64>()
                .expect("a valid ConnectionId should have a numeric counter at the end")
        });

        r.add(|_, height: u64| Height::new(0, height));
        r.add(|r, height: u64| MockHeader::new(r.make(height)));
        r.add(|r, height: u64| AnyHeader::Mock(r.make(height)));
        r.add(|r, height: u64| AnyClientState::Mock(MockClientState(r.make(height))));
        r.add(|r, height: u64| AnyConsensusState::Mock(MockConsensusState(r.make(height))));
        r.put(|_| Signer::new(""));
        r.add(|r, (client_id, connection_id): (u64, Option<u64>)| {
            Counterparty::new(
                r.make(client_id),
                connection_id.map(|id| r.make(id)),
                r.take(),
            )
        });
        r.put_as("delay_period", |_| 0u64);
        r.put::<CommitmentPrefix>(|_| vec![0].into());
        r.put::<CommitmentProofBytes>(|_| vec![0].into());
        r.add(|r, height: u64| {
            ConsensusProof::new(r.take(), r.make(height))
                .expect("it should be possible to create the consensus proof")
        });
        r.add(|r, height: u64| {
            Proofs::new(r.take(), None, Some(r.make(height)), None, r.make(height))
                .expect("it should be possible to create the proofs")
        });
        r
    }
}

#[macro_export]
macro_rules! chain_action {
    (
        $name:ident : $kind:ident
        $( $([$m:meta])* $arg:ident : $t:ty),*
    ) => {

        #[derive(Debug, Clone, PartialEq, Deserialize)]
        #[serde(rename_all = "camelCase")]
        pub struct $kind {
            $(
                $(#[$m])*
                pub $arg: $t
            
            ),*
        }

        impl ChainAction {        
            pub fn $name(chain_id: &str, $($arg: $t),*) -> ChainAction {
                ChainAction {
                    chain_id: chain_id.to_string(),
                    action: Action::$kind($kind {
                        $($arg),*
                    }),
                }
            }
        }
    };
}