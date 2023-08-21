use core::fmt::{self, Debug, Display, Error as FmtError, Formatter};
use std::{sync::Arc, time::Duration};

use ibc_proto::ibc::apps::fee::v1::{
    QueryIncentivizedPacketRequest, QueryIncentivizedPacketResponse,
};
use ibc_relayer_types::{
    applications::ics31_icq::response::CrossChainQueryResponse,
    core::{
        ics02_client::events::UpdateClient,
        ics03_connection::connection::{ConnectionEnd, IdentifiedConnectionEnd},
        ics03_connection::version::Version,
        ics04_channel::channel::{ChannelEnd, IdentifiedChannelEnd},
        ics04_channel::packet::{PacketMsgType, Sequence},
        ics23_commitment::{commitment::CommitmentPrefix, merkle::MerkleProof},
        ics24_host::identifier::ChainId,
        ics24_host::identifier::ChannelId,
        ics24_host::identifier::{ClientId, ConnectionId, PortId},
    },
    proofs::Proofs,
    signer::Signer,
    Height,
};
use std_semaphore::Semaphore;

use crate::{
    account::Balance,
    chain::{
        client::ClientSettings,
        endpoint::{ChainEndpoint, ChainStatus},
        requests::*,
        tracking::TrackedMsgs,
    },
    client_state::{AnyClientState, IdentifiedAnyClientState},
    config::ChainConfig,
    connection::ConnectionMsgType,
    consensus_state::AnyConsensusState,
    denom::DenomTrace,
    error::Error,
    event::IbcEventWithHeight,
    keyring::AnySigningKeyPair,
    light_client::AnyHeader,
    misbehaviour::MisbehaviourEvidence,
};

use super::{ChainHandle, ChainImpl, HealthCheck, Subscription};

/// A basic chain handle implementation.
/// For use in interactive CLIs, e.g., `query`, `tx`, etc.
#[derive(Clone)]
pub struct BaseChainHandle {
    /// The chain implementation
    chain: Arc<ChainImpl>,

    /// A semaphore to limit the number of concurrent requests to the chain
    semaphore: Arc<Semaphore>,
}

impl Debug for BaseChainHandle {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("BaseChainHandle")
            .field("chain_id", &self.id())
            .finish()
    }
}

impl Display for BaseChainHandle {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), FmtError> {
        write!(f, "BaseChainHandle {{ chain_id: {} }}", self.id())
    }
}

impl BaseChainHandle {
    pub fn new(chain: Arc<ChainImpl>) -> Self {
        // The semaphore is initialized with the maximum number of concurrent requests.
        // If that number was specified as 0, then we use the maximum amount of concurrency,
        // and effectively disable the limit.
        let max_concurrency = Some(chain.config().max_concurrency)
            .filter(|&n| n > 0)
            .unwrap_or(u16::MAX);

        Self {
            chain,
            semaphore: Arc::new(Semaphore::new(max_concurrency as isize)),
        }
    }
}

impl ChainHandle for BaseChainHandle {
    fn new(chain: Arc<ChainImpl>) -> Self {
        Self::new(chain)
    }

    fn id(&self) -> ChainId {
        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.id().clone(),
        }
    }

    fn health_check(&self) -> Result<HealthCheck, Error> {
        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.health_check(),
        }
    }

    fn shutdown(&self) -> Result<(), Error> {
        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.shutdown(),
        }
    }

    fn subscribe(&self) -> Result<Subscription, Error> {
        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.subscribe(),
        }
    }

    fn send_messages_and_wait_commit(
        &self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.send_messages_and_wait_commit(tracked_msgs),
        }
    }

    fn send_messages_and_wait_check_tx(
        &self,
        tracked_msgs: TrackedMsgs,
    ) -> Result<Vec<tendermint_rpc::endpoint::broadcast::tx_sync::Response>, Error> {
        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.send_messages_and_wait_check_tx(tracked_msgs),
        }
    }

    fn get_signer(&self) -> Result<Signer, Error> {
        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.get_signer(),
        }
    }

    fn config(&self) -> Result<ChainConfig, Error> {
        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => Ok(chain.config().clone()), // FIXME
        }
    }

    fn max_block_time(&self) -> Duration {
        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.max_block_time(),
        }
    }

    fn get_key(&self) -> Result<AnySigningKeyPair, Error> {
        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.get_key().map(Into::into),
        }
    }

    fn add_key(&self, key_name: String, key: AnySigningKeyPair) -> Result<(), Error> {
        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => {
                let key = key
                    .downcast()
                    .ok_or_else(|| Error::invalid_key_type(key.key_type()))?;

                chain.add_key(&key_name, key) // FIXME
            }
        }
    }

    fn ibc_version(&self) -> Result<Option<semver::Version>, Error> {
        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.ibc_version(),
        }
    }

    fn query_balance(
        &self,
        key_name: Option<String>,
        denom: Option<String>,
    ) -> Result<Balance, Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => {
                chain.query_balance(key_name.as_deref(), denom.as_deref())
            } // FIXME
        }
    }

    fn query_all_balances(&self, key_name: Option<String>) -> Result<Vec<Balance>, Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_all_balances(key_name.as_deref()), // FIXME
        }
    }

    fn query_denom_trace(&self, hash: String) -> Result<DenomTrace, Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_denom_trace(hash),
        }
    }

    fn query_application_status(&self) -> Result<ChainStatus, Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_application_status(),
        }
    }

    fn query_clients(
        &self,
        request: QueryClientStatesRequest,
    ) -> Result<Vec<IdentifiedAnyClientState>, Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_clients(request),
        }
    }

    fn query_client_state(
        &self,
        request: QueryClientStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyClientState, Option<MerkleProof>), Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_client_state(request, include_proof),
        }
    }

    fn query_client_connections(
        &self,
        request: QueryClientConnectionsRequest,
    ) -> Result<Vec<ConnectionId>, Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_client_connections(request),
        }
    }

    fn query_consensus_state_heights(
        &self,
        request: QueryConsensusStateHeightsRequest,
    ) -> Result<Vec<Height>, Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_consensus_state_heights(request),
        }
    }

    fn query_consensus_state(
        &self,
        request: QueryConsensusStateRequest,
        include_proof: IncludeProof,
    ) -> Result<(AnyConsensusState, Option<MerkleProof>), Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_consensus_state(request, include_proof),
        }
    }

    fn query_upgraded_client_state(
        &self,
        request: QueryUpgradedClientStateRequest,
    ) -> Result<(AnyClientState, MerkleProof), Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_upgraded_client_state(request),
        }
    }

    fn query_upgraded_consensus_state(
        &self,
        request: QueryUpgradedConsensusStateRequest,
    ) -> Result<(AnyConsensusState, MerkleProof), Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_upgraded_consensus_state(request),
        }
    }

    fn query_commitment_prefix(&self) -> Result<CommitmentPrefix, Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_commitment_prefix(),
        }
    }

    fn query_compatible_versions(&self) -> Result<Vec<Version>, Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_compatible_versions(),
        }
    }

    fn query_connection(
        &self,
        request: QueryConnectionRequest,
        include_proof: IncludeProof,
    ) -> Result<(ConnectionEnd, Option<MerkleProof>), Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_connection(request, include_proof),
        }
    }

    fn query_connections(
        &self,
        request: QueryConnectionsRequest,
    ) -> Result<Vec<IdentifiedConnectionEnd>, Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_connections(request),
        }
    }

    fn query_connection_channels(
        &self,
        request: QueryConnectionChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_connection_channels(request),
        }
    }

    fn query_next_sequence_receive(
        &self,
        request: QueryNextSequenceReceiveRequest,
        include_proof: IncludeProof,
    ) -> Result<(Sequence, Option<MerkleProof>), Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => {
                chain.query_next_sequence_receive(request, include_proof)
            }
        }
    }

    fn query_channels(
        &self,
        request: QueryChannelsRequest,
    ) -> Result<Vec<IdentifiedChannelEnd>, Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_channels(request),
        }
    }

    fn query_channel(
        &self,
        request: QueryChannelRequest,
        include_proof: IncludeProof,
    ) -> Result<(ChannelEnd, Option<MerkleProof>), Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_channel(request, include_proof),
        }
    }

    fn query_channel_client_state(
        &self,
        request: QueryChannelClientStateRequest,
    ) -> Result<Option<IdentifiedAnyClientState>, Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_channel_client_state(request),
        }
    }

    fn build_header(
        &self,
        trusted_height: Height,
        target_height: Height,
        client_state: AnyClientState,
    ) -> Result<(AnyHeader, Vec<AnyHeader>), Error> {
        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain
                .build_header(trusted_height, target_height, &client_state) // FIXME
                .map(|(header, support)| {
                    let header = header.into();
                    let support = support.into_iter().map(|h| h.into()).collect();
                    (header, support)
                }),
        }
    }

    fn build_client_state(
        &self,
        height: Height,
        settings: ClientSettings,
    ) -> Result<AnyClientState, Error> {
        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain
                .build_client_state(height, settings)
                .map(|cs| cs.into()),
        }
    }

    fn build_consensus_state(
        &self,
        trusted: Height,
        target: Height,
        client_state: AnyClientState,
    ) -> Result<AnyConsensusState, Error> {
        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => {
                let verified = chain.verify_header(trusted, target, &client_state)?;

                chain
                    .build_consensus_state(verified) // FIXME
                    .map(|cs| cs.into())
            }
        }
    }

    fn check_misbehaviour(
        &self,
        update_event: UpdateClient,
        client_state: AnyClientState,
    ) -> Result<Option<MisbehaviourEvidence>, Error> {
        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.check_misbehaviour(&update_event, &client_state), // FIXME
        }
    }

    fn build_connection_proofs_and_client_state(
        &self,
        message_type: ConnectionMsgType,
        connection_id: &ConnectionId,
        client_id: &ClientId,
        height: Height,
    ) -> Result<(Option<AnyClientState>, Proofs), Error> {
        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.build_connection_proofs_and_client_state(
                message_type,
                connection_id,
                client_id,
                height,
            ),
        }
    }

    fn build_channel_proofs(
        &self,
        port_id: &PortId,
        channel_id: &ChannelId,
        height: Height,
    ) -> Result<Proofs, Error> {
        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.build_channel_proofs(port_id, channel_id, height),
        }
    }

    fn build_packet_proofs(
        &self,
        packet_type: PacketMsgType,
        port_id: &PortId,
        channel_id: &ChannelId,
        sequence: Sequence,
        height: Height,
    ) -> Result<Proofs, Error> {
        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.build_packet_proofs(
                packet_type,
                port_id.clone(),
                channel_id.clone(),
                sequence,
                height,
            ),
        }
    }

    fn query_packet_commitment(
        &self,
        request: QueryPacketCommitmentRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_packet_commitment(request, include_proof),
        }
    }

    fn query_packet_commitments(
        &self,
        request: QueryPacketCommitmentsRequest,
    ) -> Result<(Vec<Sequence>, Height), Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_packet_commitments(request),
        }
    }

    fn query_packet_receipt(
        &self,
        request: QueryPacketReceiptRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_packet_receipt(request, include_proof),
        }
    }

    fn query_unreceived_packets(
        &self,
        request: QueryUnreceivedPacketsRequest,
    ) -> Result<Vec<Sequence>, Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_unreceived_packets(request),
        }
    }

    fn query_packet_acknowledgement(
        &self,
        request: QueryPacketAcknowledgementRequest,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => {
                chain.query_packet_acknowledgement(request, include_proof)
            }
        }
    }

    fn query_packet_acknowledgements(
        &self,
        request: QueryPacketAcknowledgementsRequest,
    ) -> Result<(Vec<Sequence>, Height), Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_packet_acknowledgements(request),
        }
    }

    fn query_unreceived_acknowledgements(
        &self,
        request: QueryUnreceivedAcksRequest,
    ) -> Result<Vec<Sequence>, Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_unreceived_acknowledgements(request),
        }
    }

    fn query_txs(&self, request: QueryTxRequest) -> Result<Vec<IbcEventWithHeight>, Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_txs(request),
        }
    }

    fn query_packet_events(
        &self,
        request: QueryPacketEventDataRequest,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_packet_events(request),
        }
    }

    fn query_host_consensus_state(
        &self,
        request: QueryHostConsensusStateRequest,
    ) -> Result<AnyConsensusState, Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => {
                chain.query_host_consensus_state(request).map(Into::into)
            }
        }
    }

    fn maybe_register_counterparty_payee(
        &self,
        channel_id: ChannelId,
        port_id: PortId,
        counterparty_payee: Signer,
    ) -> Result<(), Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => {
                chain.maybe_register_counterparty_payee(&channel_id, &port_id, &counterparty_payee)
            }
        }
    }

    fn cross_chain_query(
        &self,
        request: Vec<CrossChainQueryRequest>,
    ) -> Result<Vec<CrossChainQueryResponse>, Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.cross_chain_query(request),
        }
    }

    fn query_incentivized_packet(
        &self,
        request: QueryIncentivizedPacketRequest,
    ) -> Result<QueryIncentivizedPacketResponse, Error> {
        let _permit = self.semaphore.access();

        match self.chain.as_ref() {
            ChainImpl::CosmosSdk(chain) => chain.query_incentivized_packet(request),
        }
    }
}
