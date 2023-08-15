use crypto_hash::{hex_digest, Algorithm};
use eyre::eyre;
use std::collections::HashMap;
use std::sync::Arc;
use std::sync::Mutex;
use std::time::SystemTime;
use std::time::UNIX_EPOCH;

use async_trait::async_trait;
use prost::EncodeError;
use secp256k1::rand::rngs::OsRng;
use secp256k1::PublicKey;
use secp256k1::Secp256k1;
use secp256k1::SecretKey;

use ibc_relayer_all_in_one::one_for_all::traits::runtime::OfaRuntime;
use ibc_relayer_all_in_one::one_for_all::types::runtime::OfaRuntimeWrapper;
use ibc_relayer_cosmos::types::tendermint::{TendermintClientState, TendermintConsensusState};
use ibc_relayer_runtime::tokio::context::TokioRuntimeContext;
use ibc_relayer_runtime::tokio::logger::tracing::TracingLogger;
use ibc_relayer_types::core::ics03_connection::connection::ConnectionEnd;
use ibc_relayer_types::core::ics03_connection::connection::State as ConnectionState;
use ibc_relayer_types::core::ics04_channel::channel::ChannelEnd;
use ibc_relayer_types::core::ics04_channel::channel::State as ChannelState;
use ibc_relayer_types::core::ics04_channel::packet::Packet;
use ibc_relayer_types::core::ics24_host::identifier::ChannelId;
use ibc_relayer_types::core::ics24_host::identifier::PortId;
use ibc_relayer_types::core::ics24_host::identifier::{ClientId, ConnectionId};
use ibc_relayer_types::Height;

use crate::traits::solomachine::SolomachineChain;
use crate::types::error::BaseError;
use crate::types::error::Error;

const DEFAULT_DIVERSIFIER: &str = "solo-machine-diversifier";

pub struct MockSolomachineChainContext {
    commitment_prefix: String,
    public_key: PublicKey,
    secret_key: SecretKey,
    client_states: Arc<Mutex<HashMap<ClientId, TendermintClientState>>>,
    client_consensus_states: Arc<Mutex<HashMap<ClientId, TendermintConsensusState>>>,
    pub runtime: OfaRuntimeWrapper<TokioRuntimeContext>,
}

impl MockSolomachineChainContext {
    pub fn new(commitment_prefix: String, runtime: OfaRuntimeWrapper<TokioRuntimeContext>) -> Self {
        let secp = Secp256k1::new();
        let (secret_key, public_key) = secp.generate_keypair(&mut OsRng);
        MockSolomachineChainContext {
            commitment_prefix,
            public_key,
            secret_key,
            client_states: Arc::new(Mutex::new(HashMap::new())),
            client_consensus_states: Arc::new(Mutex::new(HashMap::new())),
            runtime,
        }
    }
}

#[async_trait]
impl SolomachineChain for MockSolomachineChainContext {
    type Error = Error;

    type Runtime = TokioRuntimeContext;

    type Logger = TracingLogger;

    type Diversifier = String;

    fn runtime(&self) -> &OfaRuntimeWrapper<Self::Runtime> {
        &self.runtime
    }

    fn runtime_error(e: <Self::Runtime as OfaRuntime>::Error) -> Self::Error {
        BaseError::tokio(e).into()
    }

    fn logger(&self) -> &Self::Logger {
        &TracingLogger
    }

    fn encode_error(e: EncodeError) -> Self::Error {
        BaseError::encode(e).into()
    }

    fn invalid_connection_state_error(
        expected: ConnectionState,
        actual: ConnectionState,
    ) -> Self::Error {
        BaseError::invalid_connection_state(expected, actual).into()
    }

    fn invalid_channel_state_error(expected: ChannelState, actual: ChannelState) -> Self::Error {
        BaseError::invalid_channel_state(expected, actual).into()
    }

    fn public_key(&self) -> &PublicKey {
        &self.public_key
    }

    fn secret_key(&self) -> &SecretKey {
        &self.secret_key
    }

    fn commitment_prefix(&self) -> &str {
        self.commitment_prefix.as_str()
    }

    fn current_time(&self) -> u64 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("error computing current time")
            .as_secs()
    }

    async fn new_client(&self) -> Result<ClientId, Self::Error> {
        todo!()
    }

    async fn new_diversifier(&self) -> String {
        DEFAULT_DIVERSIFIER.to_string()
    }

    async fn next_diversifier(&self, diversifier: &str) -> String {
        hex_digest(Algorithm::SHA256, diversifier.as_bytes())
    }

    async fn query_client_state(
        &self,
        client_id: &ClientId,
    ) -> Result<TendermintClientState, Self::Error> {
        let client_states = self.client_states.lock().unwrap();
        client_states
            .get(client_id)
            .ok_or_else(|| BaseError::generic(eyre!("tmp")).into())
            .cloned()
    }

    async fn query_consensus_state(
        &self,
        client_id: &ClientId,
        _height: Height,
    ) -> Result<TendermintConsensusState, Self::Error> {
        let client_consensus_statesl = self.client_consensus_states.lock().unwrap();
        client_consensus_statesl
            .get(client_id)
            .ok_or_else(|| BaseError::generic(eyre!("tmp")).into())
            .cloned()
    }

    async fn query_connection(
        &self,
        _connection_id: &ConnectionId,
    ) -> Result<ConnectionEnd, Self::Error> {
        todo!()
    }

    async fn query_channel(
        &self,
        _channel_id: &ChannelId,
        _port_id: &PortId,
    ) -> Result<ChannelEnd, Self::Error> {
        todo!()
    }

    async fn handle_receive_packet(&self, _packet: &Packet) -> Result<Vec<u8>, Self::Error> {
        todo!()
    }
}
