use prost_types::Any;
use thiserror::Error;

use ibc_proto::ibc::core::client::v1::MsgCreateClient as RawMsgCreateClient;
use ibc_proto::ibc::core::client::v1::MsgUpdateClient as RawMsgUpdateClient;

use ibc::ics02_client::header::Header;
use ibc::ics02_client::msgs::create_client::MsgCreateAnyClient;
use ibc::ics02_client::msgs::update_client::MsgUpdateAnyClient;
use ibc::ics02_client::state::ClientState;
use ibc::ics02_client::state::ConsensusState;
use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc::tx_msg::Msg;
use ibc::Height;

use crate::chain::handle::ChainHandle;
use crate::error::{Error, Kind};

#[derive(Debug, Error)]
pub enum ForeignClientError {
    #[error("error raised while creating client: {0}")]
    ClientCreate(String),

    #[error("error raised while updating client: {0}")]
    ClientUpdate(String),
}

#[derive(Clone, Debug)]
pub struct ForeignClientConfig {
    chain: ChainId,
    id: ClientId,
}

impl ForeignClientConfig {
    pub fn new(chain: &ChainId, id: &ClientId) -> ForeignClientConfig {
        Self {
            chain: chain.clone(),
            id: id.clone(),
        }
    }

    pub fn chain_id(&self) -> &ChainId {
        &self.chain
    }

    pub fn client_id(&self) -> &ClientId {
        &self.id
    }
}

#[derive(Clone)]
pub struct ForeignClient {
    config: ForeignClientConfig,
}

impl ForeignClient {
    /// Creates a new foreign client. Blocks until the client is created on `host` chain (or
    /// panics???).
    /// Post-condition: chain `host` will host an IBC client for chain `source`.
    /// TODO: what are the pre-conditions for success?
    /// Is it enough to have a "live" handle to each of `host` and `target` chains?
    pub fn new(
        host: impl ChainHandle,
        source: impl ChainHandle,
        config: ForeignClientConfig,
    ) -> Result<ForeignClient, ForeignClientError> {
        let done = '\u{1F36D}';

        // Query the client state on source chain.
        let client_state = host.query_client_state(&config.id, Height::default());
        if client_state.is_err() {
            build_create_client_and_send(source, host, &config).map_err(|e| {
                ForeignClientError::ClientCreate(format!("Create client failed ({:?})", e))
            })?;
        }
        println!(
            "{}  Client on {:?} is created {:?}\n",
            done, config.chain, config.id
        );
        Ok(ForeignClient { config })
    }

    pub fn update(
        &mut self,
        _src_chain: impl ChainHandle,
        _dst_chain: impl ChainHandle,
        src_target_height: Height,
    ) -> Result<Height, ForeignClientError> {
        /*
        return Ok(src_target_height);
        let (src_consensus_state, dst_membership_proof) =
            dst_chain.consensus_state(src_chain.id(), src_target_height);

        let dst_sh = dst_chain.get_header(dst_membership_proof.height + 1);
        // type verifyMembership = (root: CommitmentRoot, proof: CommitmentProof, path: CommitmentPath, value: Value) => boolean (ICS-023)
        if ! verify_consensus_state_inclusion(&src_consensus_state, &dst_membership_proof, &(dst_sh.header.app_hash)) {
            // Error: Destination chain provided invalid consensus_state
            return Err(ForeignClientError::VerificationError())
        }

        if src_chain.get_header(src_consensus_state.height).header == src_consensus_state.signed_header.header {
            return Err(ForeignClientError::HeaderMismatch())
        }

        while src_consensus_state.height < src_target_height {
            let src_signed_headers = src_chain.get_minimal_set(src_consensus_state.height, src_target_height);

            // if we actually want to do this we need to create a transaction
            // This might fail semantically due to competing relayers
            // Even if this fails, we need to continue
            // XXX FIXME
            dst_chain.submit(vec![create_client_update_datagram(src_signed_headers)]);

            let (src_consensus_state, dst_membership_proof) = dst_chain.consensus_state(src_chain.id(), src_target_height);
            let dst_sh = dst_chain.get_header(dst_membership_proof.height + 1);
            if ! verify_consensus_state_inclusion(&src_consensus_state, &dst_membership_proof, &(dst_sh.header.app_hash)) {
                // Error: Destination chain provided invalid client_state
                return Err(ForeignClientError::VerificationError())
            }

            if src_chain.get_header(src_consensus_state.height).header == src_consensus_state.signed_header.header {
                // Error: consesus_state isn't verified by self light client
                return  Err(ForeignClientError::HeaderMismatch())
            }
        }
        */

        Ok(src_target_height)
    }
}

pub fn build_create_client(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    dst_client_id: &ClientId,
) -> Result<MsgCreateAnyClient, Error> {
    // Verify that the client has not been created already, i.e the destination chain does not
    // have a state for this client.
    let client_state = dst_chain.query_client_state(&dst_client_id, Height::default());
    if client_state.is_ok() {
        return Err(Into::<Error>::into(Kind::CreateClient(
            dst_client_id.clone(),
            "client already exists".into(),
        )));
    }

    // Get signer
    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    // Build client create message with the data from source chain at latest height.
    let latest_height = src_chain.query_latest_height()?;
    Ok(MsgCreateAnyClient::new(
        dst_client_id.clone(),
        src_chain.build_client_state(latest_height)?.wrap_any(),
        src_chain.build_consensus_state(latest_height)?.wrap_any(),
        signer,
    )
    .map_err(|e| {
        Kind::MessageTransaction("failed to build the create client message".into()).context(e)
    })?)
}

pub fn build_create_client_and_send(
    src_chain: impl ChainHandle,
    dst_chain: impl ChainHandle,
    opts: &ForeignClientConfig,
) -> Result<String, Error> {
    let new_msg = build_create_client(dst_chain.clone(), src_chain, opts.client_id())?;

    Ok(dst_chain.send_tx(vec![new_msg.to_any::<RawMsgCreateClient>()])?)
}

pub fn build_update_client(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    dst_client_id: &ClientId,
    target_height: Height,
) -> Result<Vec<Any>, Error> {
    // Get the latest trusted height from the client state on destination.
    let trusted_height = dst_chain
        .query_client_state(&dst_client_id, Height::default())?
        .latest_height();

    let header = src_chain
        .build_header(trusted_height, target_height)?
        .wrap_any();

    let signer = dst_chain.get_signer()?;
    let new_msg = MsgUpdateAnyClient {
        client_id: dst_client_id.clone(),
        header,
        signer,
    };

    Ok(vec![new_msg.to_any::<RawMsgUpdateClient>()])
}

pub fn build_update_client_and_send(
    src_chain: impl ChainHandle,
    dst_chain: impl ChainHandle,
    opts: &ForeignClientConfig,
) -> Result<String, Error> {
    let new_msgs = build_update_client(
        dst_chain.clone(),
        src_chain.clone(),
        opts.client_id(),
        src_chain.query_latest_height()?,
    )?;

    Ok(dst_chain.send_tx(new_msgs)?)
}
