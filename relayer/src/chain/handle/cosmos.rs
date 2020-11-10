use crate::chain::handle::{ChainHandle, HandleInput, Subscription};
use crate::config::ChainConfig;
use crate::error::{Error, Kind};
use crate::foreign_client::ForeignClient;
use crate::msgs::{Datagram, EncodedTransaction, IBCEvent, Packet};
use crate::util::block_on;

use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState, AnyHeader};
use ibc::ics07_tendermint::{client_state::ClientState, consensus_state::ConsensusState};
use ibc::ics24_host::{identifier::ChainId, Path, IBC_QUERY_PATH};
use ibc::{downcast, Height};

use tendermint::abci::Path as ABCIPath;
use tendermint::block::Height as TMHeight;
use tendermint::net;
use tendermint_rpc::{Client, HttpClient};

use crossbeam_channel as channel;
use std::convert::{TryFrom, TryInto};
use std::str::FromStr;
use std::time::Duration;
use thiserror::Error;

use super::reply_channel;

/// The handle for interacting with a Cosmos chain.
///     - `sender` enables communication with the chain runtime (mainly for `subscribe`).
///     - `rpc_client` is the gateway to a full-node for fulfilling ABCI queries.
#[derive(Debug, Clone)]
pub struct CosmosSDKHandle {
    chain_id: ChainId,
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
    ) -> Result<Self, Error> {
        let rpc_client = HttpClient::new(rpc_addr).map_err(|e| {
            Kind::Rpc.context(format!(
                "could not initialize http client; error: {}",
                e.to_string()
            ))
        })?;

        let chain_id =
            ChainId::from_str(chain_id_raw).map_err(|e| Kind::ChainIdentifier(e.to_string()))?;
        let chain_version = chain_id.version();

        Ok(Self {
            chain_id,
            sender,
            rpc_client,
            trusting_period: todo!(),
            unbonding_period: todo!(),
            chain_version,
        })
    }
}

impl ChainHandle for CosmosSDKHandle {
    fn subscribe(&self, _chain_id: ChainId) -> Result<Subscription, Error> {
        let (sender, receiver) = reply_channel();
        self.sender.send(HandleInput::Subscribe(sender)).unwrap();
        receiver.recv().unwrap()
    }

    fn query(&self, data_path: Path, height: Height, prove: bool) -> Result<Vec<u8>, Error> {
        let (sender, receiver) = reply_channel();

        self.sender
            .send(HandleInput::Query {
                path: data_path,
                height,
                prove,
                reply_to: sender,
            })
            .unwrap();

        receiver.recv().unwrap()
    }

    fn get_header(&self, height: Height) -> Result<AnyHeader, Error> {
        todo!()
    }

    fn get_minimal_set(&self, from: Height, to: Height) -> Result<Vec<AnyHeader>, Error> {
        todo!()
    }

    fn submit(&self, _transaction: EncodedTransaction) -> Result<(), Error> {
        todo!()
    }

    fn get_height(&self, _client: &ForeignClient) -> Result<Height, Error> {
        todo!()
    }

    fn id(&self) -> ChainId {
        self.chain_id.clone()
    }

    fn create_packet(&self, _event: IBCEvent) -> Result<Packet, Error> {
        todo!()
    }

    fn assemble_client_state(&self, header: &AnyHeader) -> Result<AnyClientState, Error> {
        // Downcast from the generic any header into a header specific for this type of chain.
        if let Some(our_header) = downcast!(header => AnyHeader::Tendermint) {
            let height = u64::from(our_header.signed_header.header.height);

            // Build the client state.
            let client_state = ClientState::new(
                self.chain_id.to_string(), // The id of this chain.
                self.trusting_period,
                self.unbonding_period,
                Duration::from_millis(3000),
                Height::new(self.chain_version, height),
                Height::new(self.chain_version, 0),
                "".to_string(),
                false,
                false,
            )
            .map(AnyClientState::Tendermint)
            .map_err(|e| Kind::Ics007.context(e))?;

            Ok(client_state)
        } else {
            Err(Kind::InvalidInputHeader.into())
        }
    }

    fn assemble_consensus_state(&self, header: &AnyHeader) -> Result<AnyConsensusState, Error> {
        if let Some(our_header) = downcast!(header => AnyHeader::Tendermint) {
            Ok(AnyConsensusState::Tendermint(ConsensusState::from(
                our_header.signed_header.clone(),
            )))
        } else {
            Err(Kind::InvalidInputHeader.into())
        }
    }
}
