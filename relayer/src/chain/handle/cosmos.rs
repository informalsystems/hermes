use crate::chain::handle::{ChainHandle, ChainHandleError, HandleInput, Subscription};
use crate::config::ChainConfig;
use crate::foreign_client::ForeignClient;
use crate::msgs::{Datagram, EncodedTransaction, IBCEvent, Packet};
use crate::util::block_on;

use ibc::downcast;
use ibc::ics24_host::{identifier::ChainId, Path, IBC_QUERY_PATH};
use ibc::Height;

use tendermint::abci::Path as ABCIPath;
use tendermint::block::Height as TMHeight;
use tendermint::net;
use tendermint_rpc::{Client, HttpClient};

use crossbeam_channel as channel;
use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
use std::convert::{TryFrom, TryInto};
use std::str::FromStr;
use std::time::Duration;
use thiserror::Error;

/// The handle for interacting with a Cosmos chain.
/// The `sender` enables communication with the chain runtime (mainly for `subscribe`).
/// The `rpc_client` is the gateway to a full-node for fulfilling ABCI queries.
#[derive(Debug, Clone)]
pub struct CosmosSDKHandle {
    pub chain_id: ChainId,
    sender: channel::Sender<HandleInput>,
    rpc_client: HttpClient,
    trusting_period: Duration,
    unbonding_period: Duration,
    chain_version: u64, // TODO: account_prefix
}

impl CosmosSDKHandle {
    pub(crate) fn new(
        chain_id_raw: &str,
        sender: channel::Sender<HandleInput>,
        rpc_addr: net::Address,
    ) -> Result<Self, ChainHandleError> {
        let rpc_client = HttpClient::new(rpc_addr).map_err(|e| {
            ChainHandleError::RPC(format!(
                "could not initialize http client; error: {}",
                e.to_string()
            ))
        })?;
        let chain_id = ChainId::from_str(chain_id_raw)
            .map_err(|e| ChainHandleError::ChainIdentifier(e.to_string()))?;

        Ok(Self {
            chain_id,
            sender,
            rpc_client,
            trusting_period: todo!(),
            unbonding_period: todo!(),
            chain_version: ChainId::chain_version(chain_id_raw.to_string()),
        })
    }

    /// Performs a generic abci_query for , and returns the response data.
    async fn abci_query(
        &self,
        data: String,
        height: Height,
        prove: bool,
    ) -> Result<Vec<u8>, ChainHandleError> {
        let height = if height.is_zero() {
            None
        } else {
            Some(TMHeight::try_from(height.version_height).unwrap())
        };
        let path = ABCIPath::from_str(IBC_QUERY_PATH).unwrap();

        // Use the Tendermint-rs RPC client to do the query.
        let response = self
            .rpc_client
            .abci_query(Some(path), data.into_bytes(), height, prove)
            .await
            .map_err(|e| ChainHandleError::RPC(e.to_string()))?;

        if !response.code.is_ok() {
            // Fail with response log.
            return Err(ChainHandleError::RPC(response.log.to_string()));
        }
        if response.value.is_empty() {
            // Fail due to empty response value (nothing to decode).
            return Err(ChainHandleError::RPC("Empty response value".to_string()));
        }

        Ok(response.value)
    }
}

impl ChainHandle for CosmosSDKHandle {
    fn subscribe(&self, _chain_id: ChainId) -> Result<Subscription, ChainHandleError> {
        let (sender, receiver) = channel::bounded::<Subscription>(1);
        self.sender.send(HandleInput::Subscribe(sender)).unwrap();
        Ok(receiver.recv().unwrap())
    }

    fn query(
        &self,
        data_path: Path,
        height: Height,
        prove: bool,
    ) -> Result<Vec<u8>, ChainHandleError> {
        if !data_path.is_provable() & prove {
            return Err(ChainHandleError::NonProvableData);
        }

        let response = block_on(self.abci_query(data_path.to_string(), height, prove))?;

        // Verify response proof, if requested.
        if prove {
            dbg!("Todo: implement proof verification."); // Todo: Verify proof
        }

        Ok(response)
    }

    fn get_header(&self, height: Height) -> Result<AnyHeader, ChainHandleError> {
        todo!()
    }

    fn get_minimal_set(
        &self,
        from: Height,
        to: Height,
    ) -> Result<Vec<AnyHeader>, ChainHandleError> {
        todo!()
    }

    fn submit(&self, _transaction: EncodedTransaction) -> Result<(), ChainHandleError> {
        todo!()
    }

    fn get_height(&self, _client: &ForeignClient) -> Result<Height, ChainHandleError> {
        todo!()
    }

    fn id(&self) -> ChainId {
        self.chain_id.clone()
    }

    fn create_packet(&self, _event: IBCEvent) -> Result<Packet, ChainHandleError> {
        todo!()
    }

    fn assemble_client_state(
        &self,
        header: &AnyHeader,
    ) -> Result<AnyClientState, ChainHandleError> {
        // Downcast from the generic any header into a header specific for this type of chain.
        if let Some(our_header) = downcast!(header => AnyHeader::Tendermint) {
            let height = u64::from(our_header.signed_header.header.height);

            // Build the client state.
            ibc::ics07_tendermint::client_state::ClientState::new(
                self.chain_id.to_string(), // The id of this chain.
                self.trusting_period,
                self.unbonding_period,
                Duration::from_millis(3000),
                Height::new(self.chain_version, height),
                Height::new(self.chain_version, 0),
                "".to_string(),
                false,
                false,
            ) // TODO more useful err message below :(
            .map_err(|e| ChainHandleError::Failed)
            .map(AnyClientState::Tendermint)
        } else {
            Err(ChainHandleError::InvalidInputHeader)
        }
    }

    fn assemble_consensus_state(
        &self,
        header: &AnyHeader,
    ) -> Result<AnyConsensusState, ChainHandleError> {
        if let Some(our_header) = downcast!(header => AnyHeader::Tendermint) {
            Ok(AnyConsensusState::Tendermint(
                ibc::ics07_tendermint::consensus_state::ConsensusState::from(
                    our_header.signed_header.clone(),
                ),
            ))
        } else {
            Err(ChainHandleError::InvalidInputHeader)
        }
    }
}
