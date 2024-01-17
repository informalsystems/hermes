use ibc_relayer_types::core::{
    ics23_commitment::merkle::MerkleProof,
    ics24_host::identifier::ChainId,
};
use ibc_types::DomainType as _;
use tendermint_rpc::endpoint::broadcast::tx_sync::Response;

use crate::{
    chain::cosmos::types::tx::{
        TxStatus,
        TxSyncResult,
    },
    error::Error,
    event::IbcEventWithHeight,
};

pub(crate) fn decode_merkle_proof(proof_bytes: Vec<u8>) -> Result<MerkleProof, Error> {
    use ibc_types::core::commitment::MerkleProof as IbcTypesMerkleProof;

    let proof: IbcTypesMerkleProof =
        IbcTypesMerkleProof::decode::<bytes::Bytes>(proof_bytes.into())
            .map_err(|e| Error::other_with_string(e.to_string()))?;
    let proof_proto = proof.to_proto();
    proof_proto
        .try_into()
        .map_err(|e| Error::other(Box::new(e)))
}

pub(crate) fn response_to_tx_sync_result(
    chain_id: &ChainId,
    message_count: usize,
    response: Response,
) -> TxSyncResult {
    if response.code.is_err() {
        // TODO: can we remove this and just return an err in the caller?
        //
        // Note (penumbra): we don't have any height information in this case. This hack will fix itself
        // once we remove the `ChainError` event (which is not actually an event)
        let height = ibc_relayer_types::Height::new(chain_id.version(), 1).unwrap();

        let events_per_tx = vec![IbcEventWithHeight::new(ibc_relayer_types::events::IbcEvent::ChainError(format!(
            "check_tx (broadcast_tx_sync) on chain {} for Tx hash {} reports error: code={:?}, log={:?}",
            chain_id, response.hash, response.code, response.log
        )), height); message_count];

        TxSyncResult {
            response,
            events: events_per_tx,
            status: TxStatus::ReceivedResponse,
        }
    } else {
        TxSyncResult {
            response,
            events: Vec::new(),
            status: TxStatus::Pending { message_count },
        }
    }
}
