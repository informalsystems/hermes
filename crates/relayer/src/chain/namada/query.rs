use ibc_relayer_types::core::ics04_channel::packet::Sequence;
use ibc_relayer_types::core::ics23_commitment::merkle::convert_tm_to_ics_merkle_proof;
use ibc_relayer_types::core::ics23_commitment::merkle::MerkleProof;
use ibc_relayer_types::events::IbcEvent;
use ibc_relayer_types::Height as ICSHeight;
use namada_sdk::address::{Address, InternalAddress};
use namada_sdk::borsh::BorshDeserialize;
use namada_sdk::events::extend::Height as HeightAttr;
use namada_sdk::events::Event as NamadaEvent;
use namada_sdk::ibc::storage::{ibc_trace_key_prefix, is_ibc_trace_key};
use namada_sdk::io::Client;
use namada_sdk::io::NamadaIo;
use namada_sdk::queries::RPC;
use namada_sdk::rpc;
use namada_sdk::storage::{BlockHeight, Epoch, Key, PrefixValue};
use namada_sdk::tx::data::ResultCode;
use namada_sdk::tx::event::{Batch as BatchAttr, Code as CodeAttr};
use namada_tendermint::block::Height as TmHeight;
use namada_tendermint::merkle::proof::ProofOps;
use namada_tendermint::Hash as TmHash;
use namada_tendermint_proto::v0_37::abci::Event as TmEvent;

use crate::chain::endpoint::ChainEndpoint;
use crate::chain::requests::{
    IncludeProof, QueryClientEventRequest, QueryHeight, QueryPacketEventDataRequest,
};
use crate::error::Error;
use crate::event::{ibc_event_try_from_abci_event, IbcEventWithHeight};

use super::error::Error as NamadaError;
use super::NamadaChain;

impl NamadaChain {
    pub fn query(
        &self,
        key: Key,
        height: QueryHeight,
        include_proof: IncludeProof,
    ) -> Result<(Vec<u8>, Option<MerkleProof>), Error> {
        let height = match height {
            QueryHeight::Latest => None,
            QueryHeight::Specific(h) => Some(BlockHeight(h.revision_height())),
        };
        let is_proven = matches!(include_proof, IncludeProof::Yes);
        let (value, proof) = self
            .rt
            .block_on(rpc::query_storage_value_bytes(
                self.ctx.client(),
                &key,
                height,
                is_proven,
            ))
            .map_err(NamadaError::namada)?;

        let proof = if is_proven {
            let proof_ops = proof.ok_or_else(Error::empty_response_proof)?;
            let tm_proof_ops = into_tm_proof(proof_ops);
            let proof = convert_tm_to_ics_merkle_proof(&tm_proof_ops).map_err(Error::ics23)?;
            Some(proof)
        } else {
            None
        };
        // return an empty data for non-existence proof
        Ok((value.unwrap_or_default(), proof))
    }

    pub fn query_prefix(&self, prefix: Key) -> Result<Vec<PrefixValue>, Error> {
        let response = self
            .rt
            .block_on(
                // We can't use rpc::query_storage_prefix` because we need byte data
                RPC.shell()
                    .storage_prefix(self.ctx.client(), None, None, false, &prefix),
            )
            .map_err(NamadaError::query)?;
        Ok(response.data)
    }

    pub fn query_epoch(&self) -> Result<Epoch, Error> {
        self.rt
            .block_on(rpc::query_epoch(self.ctx.client()))
            .map_err(|e| Error::namada(NamadaError::namada(e)))
    }

    pub fn query_update_event(
        &self,
        request: &QueryClientEventRequest,
    ) -> Result<Option<IbcEventWithHeight>, Error> {
        let height = BlockHeight(request.consensus_height.revision_height());
        let event = self
            .rt
            .block_on(RPC.shell().ibc_client_update(
                self.ctx.client(),
                &request.client_id.as_str().parse().unwrap(),
                &height,
            ))
            .map_err(NamadaError::query)?;
        match event {
            Some(event) => {
                let h = event
                    .read_attribute::<HeightAttr>()
                    .map_err(|_| Error::invalid_height_no_source())?;
                let height = ICSHeight::new(self.config.id.version(), h.0)
                    .map_err(|_| Error::invalid_height_no_source())?;
                let pb_abci_event = TmEvent::from(event);
                let abci_event = into_abci_event(pb_abci_event);
                match ibc_event_try_from_abci_event(&abci_event) {
                    Ok(event) => Ok(Some(IbcEventWithHeight { event, height })),
                    // non IBC event
                    Err(_) => Ok(None),
                }
            }
            None => Ok(None),
        }
    }

    /// Get all IBC events when the tx has been applied
    pub fn query_tx_events(&self, tx_hash: &TmHash) -> Result<Vec<IbcEventWithHeight>, Error> {
        match self.query_applied_event(tx_hash)? {
            Some(applied) => {
                let h = applied
                    .read_attribute::<HeightAttr>()
                    .map_err(|_| Error::invalid_height_no_source())?;
                let height = ICSHeight::new(self.config.id.version(), h.0)
                    .map_err(|_| Error::invalid_height_no_source())?;
                // Check if the tx is valid
                let tx_result = applied
                    .read_attribute::<BatchAttr<'_>>()
                    .expect("The batch attribute should exist");
                let code = applied
                    .read_attribute::<CodeAttr>()
                    .expect("The code attribute should exist");
                if code != ResultCode::Ok {
                    return Ok(vec![IbcEventWithHeight::new(
                        IbcEvent::ChainError(format!(
                            "The transaction was invalid: TxResult {tx_result}",
                        )),
                        height,
                    )]);
                }
                let events = tx_result.iter().filter_map(|(_, r)| {
                    r.as_ref().map(|batched_tx_result| {
                        // Get IBC events when the transaction was accepted
                        if batched_tx_result.is_accepted() {
                            batched_tx_result.events.iter().filter_map(|event| {
                                let pb_abci_event = TmEvent::from(event.clone());
                                let abci_event = into_abci_event(pb_abci_event);
                                ibc_event_try_from_abci_event(&abci_event).ok()
                            }).map(|ibc_event| IbcEventWithHeight::new(ibc_event, height)).collect()
                        } else {
                            vec![IbcEventWithHeight::new(
                                IbcEvent::ChainError(format!(
                                    "The transaction was invalid: BatchedTxResult {batched_tx_result}",
                                )),
                                height,
                            )]
                        }
                    }).ok()
                }).flatten().collect();
                Ok(events)
            }
            None => Ok(vec![]),
        }
    }

    fn query_applied_event(&self, tx_hash: &TmHash) -> Result<Option<NamadaEvent>, Error> {
        self.rt
            .block_on(RPC.shell().applied(
                self.ctx.client(),
                &tx_hash.as_ref().try_into().expect("Invalid tx hash"),
            ))
            .map_err(|e| Error::namada(NamadaError::query(e)))
    }

    /// Get IBC packet events
    pub fn query_packet_events_from_block(
        &self,
        request: &QueryPacketEventDataRequest,
    ) -> Result<Vec<IbcEventWithHeight>, Error> {
        let mut block_events = vec![];
        for seq in &request.sequences {
            if let Some(response_height) = self.query_packet_height(request, *seq)? {
                if let QueryHeight::Specific(query_height) = request.height.get() {
                    if response_height > query_height {
                        continue;
                    }
                }
                let events = self.query_events(response_height)?;
                let mut packet_events = events
                    .into_iter()
                    .filter(|e| {
                        let packet = match &e.event {
                            IbcEvent::SendPacket(send_event) => &send_event.packet,
                            IbcEvent::WriteAcknowledgement(write_ack_event) => {
                                &write_ack_event.packet
                            }
                            _ => return false,
                        };
                        !block_events.contains(e)
                            && packet.source_port == request.source_port_id
                            && packet.source_channel == request.source_channel_id
                            && packet.destination_port == request.destination_port_id
                            && packet.destination_channel == request.destination_channel_id
                            && packet.sequence == *seq
                    })
                    .collect();
                block_events.append(&mut packet_events);
            }
        }
        Ok(block_events)
    }

    /// Get the height at which the packet event has been emitted
    fn query_packet_height(
        &self,
        request: &QueryPacketEventDataRequest,
        sequence: Sequence,
    ) -> Result<Option<ICSHeight>, Error> {
        match self
            .rt
            .block_on(
                RPC.shell().ibc_packet(
                    self.ctx.client(),
                    &request
                        .event_id
                        .as_str()
                        .parse()
                        .expect("invalid event type"),
                    &request
                        .source_port_id
                        .as_str()
                        .parse()
                        .expect("PortId should be parsable"),
                    &request
                        .source_channel_id
                        .as_str()
                        .parse()
                        .expect("ChannelId should be parsable"),
                    &request
                        .destination_port_id
                        .as_str()
                        .parse()
                        .expect("PortId should be parsable"),
                    &request
                        .destination_channel_id
                        .as_str()
                        .parse()
                        .expect("ChannelId should be parsable"),
                    &u64::from(sequence).into(),
                ),
            )
            .map_err(NamadaError::query)?
        {
            Some(event) => {
                let h = event
                    .read_attribute::<HeightAttr>()
                    .map_err(|_| Error::invalid_height_no_source())?;
                let height = ICSHeight::new(self.config.id.version(), h.0)
                    .map_err(|_| Error::invalid_height_no_source())?;
                Ok(Some(height))
            }
            None => Ok(None),
        }
    }

    /// Get IBC events at the given height
    fn query_events(&self, height: ICSHeight) -> Result<Vec<IbcEventWithHeight>, Error> {
        crate::time!(
            "query_blocks: query block packet events",
            {
                "src_chain": self.config.id.to_string(),
            }
        );
        crate::telemetry!(query, self.id(), "query_block");

        let tm_height = TmHeight::try_from(height.revision_height())
            .map_err(|_| Error::invalid_height_no_source())?;
        let response = self
            .rt
            .block_on(Client::block_results(self.ctx.client(), tm_height))
            .map_err(|e| NamadaError::rpc(self.config.rpc_addr.clone(), e))?;

        let events = response
            .end_block_events
            .ok_or_else(|| Error::query("No transaction result was found".to_string()))?;
        let mut ibc_events = vec![];
        for event in events {
            let pb_abci_event = TmEvent::from(event);
            let abci_event = into_abci_event(pb_abci_event);
            if let Ok(ibc_event) = ibc_event_try_from_abci_event(&abci_event) {
                ibc_events.push(IbcEventWithHeight::new(ibc_event, height))
            }
        }
        Ok(ibc_events)
    }

    /// Get IBC denom
    pub fn query_denom(&self, raw_addr: String) -> Result<String, Error> {
        let token = Address::decode(&raw_addr)
            .map_err(|_| NamadaError::address_decode(raw_addr.to_string()))?;
        let hash = match &token {
            Address::Internal(InternalAddress::IbcToken(hash)) => hash.to_string(),
            _ => return Err(NamadaError::denom_not_found(raw_addr).into()),
        };

        let prefix = ibc_trace_key_prefix(None);
        let pairs = self.query_prefix(prefix)?;
        let pair = pairs
            .iter()
            .find(|PrefixValue { key, value: _ }| {
                if let Some((_, token_hash)) = is_ibc_trace_key(key) {
                    token_hash == *hash
                } else {
                    false
                }
            })
            .ok_or(NamadaError::denom_not_found(raw_addr))?;

        String::try_from_slice(&pair.value).map_err(|e| Error::namada(NamadaError::borsh_decode(e)))
    }
}

fn into_tm_proof(proof_ops: ProofOps) -> tendermint::merkle::proof::ProofOps {
    let ops = proof_ops
        .ops
        .into_iter()
        .map(|op| tendermint::merkle::proof::ProofOp {
            field_type: op.field_type,
            key: op.key,
            data: op.data,
        })
        .collect();
    tendermint::merkle::proof::ProofOps { ops }
}

fn into_abci_event(event: TmEvent) -> tendermint::abci::Event {
    let attributes = event
        .attributes
        .into_iter()
        .map(|attribute| (attribute.key, attribute.value).into())
        .collect();
    tendermint::abci::Event {
        kind: event.r#type,
        attributes,
    }
}
