use prost_types::Any;
use thiserror::Error;

use ibc::ics02_client::header::Header;
use ibc::ics02_client::msgs::create_client::MsgCreateAnyClient;
use ibc::ics02_client::msgs::update_client::MsgUpdateAnyClient;
use ibc::ics02_client::state::ClientState;
use ibc::ics02_client::state::ConsensusState;
use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc::tx_msg::Msg;
use ibc::Height;
use ibc_proto::ibc::core::client::v1::MsgCreateClient as RawMsgCreateClient;
use ibc_proto::ibc::core::client::v1::MsgUpdateClient as RawMsgUpdateClient;

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
    /// The identifier of the chain which hosts this client
    chain: ChainId,

    /// The client's identifier
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

#[derive(Clone, Debug)]
pub struct ForeignClient {
    config: ForeignClientConfig,
}

impl ForeignClient {
    /// Creates a new foreign client. Blocks until the client is created on `dst_chain` or
    /// an error occurs.
    /// Post-condition: `dst_chain` hosts an IBC client for `src_chain`.
    /// TODO: what are the pre-conditions for success?
    /// Is it enough to have a "live" handle to each of `dst_chain` and `src_chain` chains?
    pub fn new(
        dst_chain: &impl ChainHandle,
        src_chain: &impl ChainHandle,
        config: ForeignClientConfig,
    ) -> Result<ForeignClient, ForeignClientError> {
        let done = '\u{1F36D}';

        // Query the client state on source chain.
        let client_state = dst_chain.query_client_state(&config.id, Height::default());
        if client_state.is_err() {
            build_create_client_and_send(dst_chain, src_chain, &config).map_err(|e| {
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
    dst_chain: &impl ChainHandle,
    src_chain: &impl ChainHandle,
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
    dst_chain: &impl ChainHandle,
    src_chain: &impl ChainHandle,
    opts: &ForeignClientConfig,
) -> Result<String, Error> {
    let new_msg = build_create_client(dst_chain, src_chain, opts.client_id())?;

    Ok(dst_chain.send_tx(vec![new_msg.to_any::<RawMsgCreateClient>()])?)
}

pub fn build_update_client(
    dst_chain: &impl ChainHandle,
    src_chain: &impl ChainHandle,
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
    dst_chain: &impl ChainHandle,
    src_chain: &impl ChainHandle,
    opts: &ForeignClientConfig,
) -> Result<String, Error> {
    let new_msgs = build_update_client(
        dst_chain,
        src_chain,
        opts.client_id(),
        src_chain.query_latest_height()?,
    )?;

    Ok(dst_chain.send_tx(new_msgs)?)
}

/// Tests the integration of crates `relayer` plus `relayer-cli` against crate `ibc`. These tests
/// exercise various client methods (create, update, ForeignClient::new) using locally-running
/// instances of chains built using `MockChain`.
#[cfg(test)]
mod test {
    use std::str::FromStr;

    use ibc::ics24_host::identifier::ClientId;
    use ibc::Height;

    use crate::chain::handle::ChainHandle;
    use crate::chain::mock::test_utils::get_basic_chain_config;
    use crate::chain::mock::MockChain;
    use crate::chain::runtime::ChainRuntime;
    use crate::foreign_client::{
        build_create_client_and_send, build_update_client_and_send, ForeignClient,
        ForeignClientConfig,
    };

    /// Basic test for the `build_create_client_and_send` method.
    #[test]
    fn create_client_and_send_method() {
        let a_client_id = ClientId::from_str("client_on_a_forb").unwrap();
        let b_client_id = ClientId::from_str("client_on_b_fora").unwrap();
        let a_cfg = get_basic_chain_config("chain_a");
        let b_cfg = get_basic_chain_config("chain_b");
        let a_opts = ForeignClientConfig::new(&a_cfg.id, &a_client_id);
        let b_opts = ForeignClientConfig::new(&b_cfg.id, &b_client_id);

        let (a_chain, _) = ChainRuntime::<MockChain>::spawn(a_cfg).unwrap();
        let (b_chain, _) = ChainRuntime::<MockChain>::spawn(b_cfg).unwrap();

        // Create the client on chain a
        let res = build_create_client_and_send(&a_chain, &b_chain, &a_opts);
        assert!(
            res.is_ok(),
            "build_create_client_and_send failed (chain a) with error {:?}",
            res
        );

        // Double client creation should be forbidden.
        let res = build_create_client_and_send(&a_chain, &b_chain, &a_opts);
        assert!(
            res.is_err(),
            "build_create_client_and_send double client creation should have failed!",
        );

        // Create the client on chain b
        let res = build_create_client_and_send(&b_chain, &a_chain, &b_opts);
        assert!(
            res.is_ok(),
            "build_create_client_and_send failed (chain b) with error {:?}",
            res
        );

        // Test double creation for chain b
        let res = build_create_client_and_send(&b_chain, &a_chain, &b_opts);
        assert!(
            res.is_err(),
            "build_create_client_and_send failed (chain b) with error {:?}",
            res
        );
    }

    /// Basic test for the `build_update_client_and_send` & `build_create_client_and_send` methods.
    #[test]
    fn update_client_and_send_method() {
        let a_cfg = get_basic_chain_config("chain_a");
        let b_cfg = get_basic_chain_config("chain_b");
        let a_client_id = ClientId::from_str("client_on_a_forb").unwrap();
        let a_opts = ForeignClientConfig::new(&a_cfg.id, &a_client_id);
        let b_client_id = ClientId::from_str("client_on_b_fora").unwrap();
        let b_opts = ForeignClientConfig::new(&b_cfg.id, &b_client_id);

        // The number of ping-pong iterations
        let num_iterations = 3;

        let (a_chain, _) = ChainRuntime::<MockChain>::spawn(a_cfg).unwrap();
        let (b_chain, _) = ChainRuntime::<MockChain>::spawn(b_cfg).unwrap();

        // This action should fail because no client exists (yet)
        let res = build_update_client_and_send(&a_chain, &b_chain, &a_opts);
        assert!(
            res.is_err(),
            "build_update_client_and_send was supposed to fail (no client existed)"
        );

        // Remember b's height.
        let b_height_start = b_chain.query_latest_height().unwrap();

        // Create a client on chain a
        let res = build_create_client_and_send(&a_chain, &b_chain, &a_opts);
        assert!(
            res.is_ok(),
            "build_create_client_and_send failed (chain a) with error {:?}",
            res
        );

        // This should fail because the client on chain a already has the latest headers. Chain b,
        // the source chain for the client on a, is at the same height where it was when the client
        // was created, so an update should fail here.
        let res = build_update_client_and_send(&a_chain, &b_chain, &a_opts);

        assert!(
            res.is_err(),
            "build_update_client_and_send was supposed to fail",
        );
        let b_height_last = b_chain.query_latest_height().unwrap();
        assert_eq!(b_height_last, b_height_start);

        // Create a client on chain b
        let res = build_create_client_and_send(&b_chain, &a_chain, &b_opts);
        assert!(
            res.is_ok(),
            "build_create_client_and_send failed (chain b) with error {:?}",
            res
        );
        // Chain b should have advanced
        let mut b_height_last = b_chain.query_latest_height().unwrap();
        assert_eq!(b_height_last, b_height_start.increment());

        // Remember the current height of chain a
        let mut a_height_last = a_chain.query_latest_height().unwrap();

        // Now we can update both clients -- a ping pong, similar to ICS18 `client_update_ping_pong`
        for _i in 1..num_iterations {
            let res = build_update_client_and_send(&a_chain, &b_chain, &a_opts);
            assert!(
                res.is_ok(),
                "build_update_client_and_send failed (chain a) with error: {:?}",
                res
            );
            let a_height_current = a_chain.query_latest_height().unwrap();
            a_height_last = a_height_last.increment();
            assert_eq!(
                a_height_last, a_height_current,
                "after client update, chain a did not advance"
            );

            // And also update the client on chain b.
            let res = build_update_client_and_send(&b_chain, &a_chain, &b_opts);
            assert!(
                res.is_ok(),
                "build_update_client_and_send failed (chain b) with error: {:?}",
                res
            );
            let b_height_current = b_chain.query_latest_height().unwrap();
            b_height_last = b_height_last.increment();
            assert_eq!(
                b_height_last, b_height_current,
                "after client update, chain b did not advance"
            );
        }
    }

    /// Tests for `ForeignClient::new()`.
    #[test]
    fn foreign_client_create() {
        let a_cfg = get_basic_chain_config("chain_a");
        let b_cfg = get_basic_chain_config("chain_b");
        let a_client_id = ClientId::from_str("client_on_a_forb").unwrap();
        let a_opts = ForeignClientConfig::new(&a_cfg.id, &a_client_id);
        let b_client_id = ClientId::from_str("client_on_b_fora").unwrap();
        let b_opts = ForeignClientConfig::new(&b_cfg.id, &b_client_id);

        let (a_chain, _) = ChainRuntime::<MockChain>::spawn(a_cfg).unwrap();
        let (b_chain, _) = ChainRuntime::<MockChain>::spawn(b_cfg).unwrap();

        // Instantiate the foreign clients on the two chains.
        let client_on_a = ForeignClient::new(&a_chain, &b_chain, a_opts);
        assert!(
            client_on_a.is_ok(),
            "Client creation (on chain a) failed with error: {:?}",
            client_on_a
        );

        let client_on_b = ForeignClient::new(&b_chain, &a_chain, b_opts);
        assert!(
            client_on_b.is_ok(),
            "Client creation (on chain a) failed with error: {:?}",
            client_on_b
        );

        // Now that the clients exists, we should be able to query its state
        let b_client_state = b_chain.query_client_state(&b_client_id, Height::default());
        assert!(
            b_client_state.is_ok(),
            "Client query (on chain b) failed with error: {:?}",
            b_client_state
        );

        let a_client_state = a_chain.query_client_state(&a_client_id, Height::default());
        assert!(
            a_client_state.is_ok(),
            "Client query (on chain a) failed with error: {:?}",
            a_client_state
        );
    }
}
