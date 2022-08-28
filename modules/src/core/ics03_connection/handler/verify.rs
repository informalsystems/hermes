//! ICS3 verification functions, common across all four handlers of ICS3.
use crate::clients::host_functions::HostFunctionsProvider;
#[cfg(feature = "ics11_beefy")]
use crate::core::ics02_client::client_consensus::ConsensusState;
use crate::core::ics02_client::client_state::{AnyClientState, ClientState};
use crate::core::ics02_client::client_type::ClientType;
use crate::core::ics02_client::{client_def::AnyClient, client_def::ClientDef};
use crate::core::ics03_connection::connection::ConnectionEnd;
use crate::core::ics03_connection::error::Error;
use crate::core::ics23_commitment::commitment::CommitmentProofBytes;
use crate::core::ics26_routing::context::ReaderContext;
use crate::proofs::ConsensusProof;
use crate::Height;
use codec::{Decode, Encode};

/// Connection proof type, used in relayer
#[derive(Encode, Decode)]
pub struct ConnectionProof {
    pub host_proof: Vec<u8>,
    pub connection_proof: Vec<u8>,
}

/// Verifies the authenticity and semantic correctness of a commitment `proof`. The commitment
/// claims to prove that an object of type connection exists on the source chain (i.e., the chain
/// which created this proof). This object must match the state of `expected_conn`.
pub fn verify_connection_proof<HostFunctions: HostFunctionsProvider>(
    ctx: &dyn ReaderContext,
    height: Height,
    connection_end: &ConnectionEnd,
    expected_conn: &ConnectionEnd,
    proof_height: Height,
    proof: &CommitmentProofBytes,
) -> Result<(), Error> {
    // Fetch the client state (IBC client on the local/host chain).
    let client_state = ctx
        .client_state(connection_end.client_id())
        .map_err(Error::ics02_client)?;

    // The client must not be frozen.
    if client_state.is_frozen() {
        return Err(Error::frozen_client(connection_end.client_id().clone()));
    }

    // The client must have the consensus state for the height where this proof was created.
    let consensus_state = ctx
        .consensus_state(connection_end.client_id(), proof_height)
        .map_err(|e| Error::consensus_state_verification_failure(proof_height, e))?;

    // A counterparty connection id of None causes `unwrap()` below and indicates an internal
    // error as this is the connection id on the counterparty chain that must always be present.
    let connection_id = connection_end
        .counterparty()
        .connection_id()
        .ok_or_else(Error::invalid_counterparty)?;

    let client_def = AnyClient::<HostFunctions>::from_client_type(client_state.client_type());

    // Verify the proof for the connection state against the expected connection end.
    client_def
        .verify_connection_state(
            ctx,
            connection_end.client_id(),
            &client_state,
            height,
            connection_end.counterparty().prefix(),
            proof,
            consensus_state.root(),
            connection_id,
            expected_conn,
        )
        .map_err(Error::verify_connection_state)
}

/// Verifies the client `proof` from a connection handshake message, typically from a
/// `MsgConnectionOpenTry` or a `MsgConnectionOpenAck`. The `expected_client_state` argument is a
/// representation for a client of the current chain (the chain handling the current message), which
/// is running on the counterparty chain (the chain which sent this message). This method does a
/// complete verification: that the client state the counterparty stores is valid (i.e., not frozen,
/// at the same revision as the current chain, with matching chain identifiers, etc) and that the
/// `proof` is correct.
pub fn verify_client_proof<HostFunctions: HostFunctionsProvider>(
    ctx: &dyn ReaderContext,
    height: Height,
    connection_end: &ConnectionEnd,
    expected_client_state: AnyClientState,
    proof_height: Height,
    proof: &CommitmentProofBytes,
) -> Result<(), Error> {
    // Fetch the local client state (IBC client running on the host chain).
    let client_state = ctx
        .client_state(connection_end.client_id())
        .map_err(Error::ics02_client)?;

    if client_state.is_frozen() {
        return Err(Error::frozen_client(connection_end.client_id().clone()));
    }

    let consensus_state = ctx
        .consensus_state(connection_end.client_id(), proof_height)
        .map_err(|e| Error::consensus_state_verification_failure(proof_height, e))?;

    let client_def = AnyClient::<HostFunctions>::from_client_type(client_state.client_type());

    client_def
        .verify_client_full_state(
            ctx,
            &client_state,
            height,
            connection_end.counterparty().prefix(),
            proof,
            consensus_state.root(),
            connection_end.counterparty().client_id(),
            &expected_client_state,
        )
        .map_err(|e| {
            Error::client_state_verification_failure(connection_end.client_id().clone(), e)
        })
}

pub fn verify_consensus_proof<HostFunctions: HostFunctionsProvider>(
    ctx: &dyn ReaderContext,
    height: Height,
    connection_end: &ConnectionEnd,
    proof: &ConsensusProof,
) -> Result<(), Error> {
    // Fetch the client state (IBC client on the local chain).
    let client_state = ctx
        .client_state(connection_end.client_id())
        .map_err(Error::ics02_client)?;

    if client_state.is_frozen() {
        return Err(Error::frozen_client(connection_end.client_id().clone()));
    }

    let consensus_state = ctx
        .consensus_state(connection_end.client_id(), height)
        .map_err(|e| Error::consensus_state_verification_failure(height, e))?;

    let client = AnyClient::<HostFunctions>::from_client_type(client_state.client_type());

    let (consensus_proof, expected_consensus) = match ctx.host_client_type() {
        #[cfg(feature = "ics11_beefy")]
        ClientType::Beefy => {
            // if the host is beefy or near, we need to decode the proof before passing it on.
            let connection_proof: ConnectionProof =
                codec::Decode::decode(&mut proof.proof().as_bytes()).map_err(|e| {
                    Error::implementation_specific(format!("failed to decode: {:?}", e))
                })?;
            // Fetch the expected consensus state from the historical (local) header data.
            let expected_consensus = ctx
                .host_consensus_state(proof.height(), Some(connection_proof.host_proof))
                .map_err(|e| Error::consensus_state_verification_failure(proof.height(), e))?;
            (
                CommitmentProofBytes::try_from(connection_proof.connection_proof).map_err(|e| {
                    Error::implementation_specific(format!("empty proof bytes: {:?}", e))
                })?,
                expected_consensus,
            )
        }
        _ => (
            proof.proof().clone(),
            ctx.host_consensus_state(proof.height(), None)
                .map_err(|e| Error::consensus_state_verification_failure(proof.height(), e))?,
        ),
    };

    client
        .verify_client_consensus_state(
            ctx,
            &client_state,
            height,
            connection_end.counterparty().prefix(),
            &consensus_proof,
            consensus_state.root(),
            connection_end.counterparty().client_id(),
            proof.height(),
            &expected_consensus,
        )
        .map_err(|e| Error::consensus_state_verification_failure(proof.height(), e))?;

    Ok(())
}

/// Checks that `claimed_height` is within normal bounds, i.e., fresh enough so that the chain has
/// not pruned it yet, but not newer than the current (actual) height of the local chain.
pub fn check_client_consensus_height(
    ctx: &dyn ReaderContext,
    claimed_height: Height,
) -> Result<(), Error> {
    if claimed_height > ctx.host_height() {
        // Fail if the consensus height is too advanced.
        return Err(Error::invalid_consensus_height(
            claimed_height,
            ctx.host_height(),
        ));
    }

    if claimed_height < ctx.host_oldest_height() {
        // Fail if the consensus height is too old (has been pruned).
        return Err(Error::stale_consensus_height(
            claimed_height,
            ctx.host_oldest_height(),
        ));
    }

    // Height check is within normal bounds, check passes.
    Ok(())
}
