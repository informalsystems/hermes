use prost_types::Any;
use thiserror::Error;
use tracing::info;

use ibc::ics02_client::header::Header;
use ibc::ics02_client::msgs::create_client::MsgCreateAnyClient;
use ibc::ics02_client::msgs::update_client::MsgUpdateAnyClient;
use ibc::ics02_client::state::ClientState;
use ibc::ics02_client::state::ConsensusState;
use ibc::ics24_host::identifier::ClientId;
use ibc::tx_msg::Msg;
use ibc::Height;
use ibc_proto::ibc::core::client::v1::MsgCreateClient as RawMsgCreateClient;
use ibc_proto::ibc::core::client::v1::MsgUpdateClient as RawMsgUpdateClient;

use crate::chain::handle::ChainHandle;
use crate::error::{Error, Kind};
use std::str::FromStr;

#[derive(Debug, Error)]
pub enum ForeignClientError {
    #[error("error raised while creating client: {0}")]
    ClientCreate(String),

    #[error("error raised while updating client: {0}")]
    ClientUpdate(String),
}

#[derive(Clone, Debug)]
pub struct ForeignClient {
    /// The identifier of this client. The host chain determines this id upon client creation,
    /// so it may be missing (`None).
    id: Option<ClientId>,

    /// A handle to the chain hosting this client, i.e., destination chain.
    dst_chain: Box<dyn ChainHandle>,

    /// A handle to the chain whose headers this client is verifying, aka the source chain.
    src_chain: Box<dyn ChainHandle>,
}

impl ForeignClient {
    /// Creates a new foreign client on `host_chain`. Blocks until the client is created, or
    /// an error occurs.
    /// Post-condition: `host_chain` hosts an IBC client for `src_chain`.
    /// TODO: what are the pre-conditions for success?
    /// Is it enough to have a "live" handle to each of `host_chain` and `src_chain` chains?
    pub fn new(
        dst_chain: Box<dyn ChainHandle>,
        src_chain: Box<dyn ChainHandle>,
    ) -> Result<ForeignClient, ForeignClientError> {
        let mut client = ForeignClient {
            id: None,
            dst_chain: dst_chain.clone(),
            src_chain: src_chain.clone(),
        };

        client.create()?;

        Ok(client)
    }

    pub fn id(&self) -> Option<ClientId> {
        self.id.clone()
    }

    /// Sends the client creation transaction & subsequently sets the id of this ForeignClient
    fn create(&mut self) -> Result<(), ForeignClientError> {
        let done = '\u{1F36D}';

        let client_id =
            build_create_client_and_send(self.dst_chain.clone(), self.src_chain.clone()).map_err(
                |e| ForeignClientError::ClientCreate(format!("Create client failed ({:?})", e)),
            )?;

        info!(
            "{}  Client id {:?} on {:?} is created {:?}\n",
            done, client_id, self.dst_chain, self.id
        );

        self.id = Some(client_id);

        Ok(())
    }

    /// Returns a handle to the chain hosting this client.
    pub fn dst_chain(&self) -> Box<dyn ChainHandle> {
        self.dst_chain.clone()
    }

    /// Returns a handle to the chain whose headers this client is sourcing (the source chain).
    pub fn src_chain(&self) -> Box<dyn ChainHandle> {
        self.src_chain.clone()
    }

    /// Creates a message for updating this client with the latest header of its source chain.
    pub fn prepare_update(&self) -> Result<Vec<Any>, ForeignClientError> {
        let client_id = self.id.clone().ok_or_else(|| {
            ForeignClientError::ClientUpdate(
                "Client identifier not established for this ForeignClient!".to_string(),
            )
        })?;

        let target_height = self.src_chain.query_latest_height().map_err(|e| {
            ForeignClientError::ClientUpdate(format!("error querying latest height {:?}", e))
        })?;
        let msg = build_update_client(
            self.dst_chain.clone(),
            self.src_chain.clone(),
            &client_id,
            target_height,
        )
        .map_err(|e| {
            ForeignClientError::ClientUpdate(format!("build_update_client error {:?}", e))
        })?;

        Ok(msg)
    }

    /// Attempts to update a client using header from the latest height of its source chain.
    pub fn update(&self) -> Result<(), ForeignClientError> {
        let client_id = self.id.clone().ok_or_else(|| {
            ForeignClientError::ClientUpdate(
                "Client identifier not established for this ForeignClient!".to_string(),
            )
        })?;

        let res = build_update_client_and_send(
            self.dst_chain.clone(),
            self.src_chain.clone(),
            &client_id,
        )
        .map_err(|e| {
            ForeignClientError::ClientUpdate(format!("build_create_client_and_send {:?}", e))
        })?;

        println!(
            "Client id {:?} on {:?} updated with return message {:?}\n",
            client_id,
            self.dst_chain.id(),
            res
        );

        Ok(())
    }
}

/// Lower-level interface for preparing a message to create a client.
///
/// ## Note
/// Methods in `ForeignClient` (see `new`) should be preferred over this.
pub fn build_create_client(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
) -> Result<MsgCreateAnyClient, Error> {
    // Get signer
    let signer = dst_chain
        .get_signer()
        .map_err(|e| Kind::KeyBase.context(e))?;

    // Build client create message with the data from source chain at latest height.
    let latest_height = src_chain.query_latest_height()?;
    Ok(MsgCreateAnyClient::new(
        src_chain.build_client_state(latest_height)?.wrap_any(),
        src_chain.build_consensus_state(latest_height)?.wrap_any(),
        signer,
    )
    .map_err(|e| {
        Kind::MessageTransaction("failed to build the create client message".into()).context(e)
    })?)
}

/// Lower-level interface for creating a client.
/// Returns the identifier of the newly created client.
///
/// ## Note
/// Methods in `ForeignClient` (see `new`) should be preferred over this.
pub fn build_create_client_and_send(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
) -> Result<ClientId, Error> {
    let new_msg = build_create_client(dst_chain.clone(), src_chain)?;

    // Parse the client identifier out of the result vector.
    let mut result = dst_chain.send_msgs(vec![new_msg.to_any::<RawMsgCreateClient>()])?;
    let client_id_raw = result.pop().ok_or(Kind::EmptyResponseValue)?;

    ClientId::from_str(client_id_raw.as_str()).map_err(|e| {
        Kind::CreateClient(format!("generated client id {:?}", client_id_raw))
            .context(e)
            .into()
    })
}

/// Lower-level interface to create the message for updating a client to height `target_height`.
///
/// ## Note
/// Methods in `ForeignClient`, in particular `prepare_update`, should be preferred over this.
pub fn build_update_client(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
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

/// Lower-level interface for preparing a message to update a client.
///
/// ## Note
/// Methods in `ForeignClient` (see `update`) should be preferred over this.
pub fn build_update_client_and_send(
    dst_chain: Box<dyn ChainHandle>,
    src_chain: Box<dyn ChainHandle>,
    dst_client_id: &ClientId,
) -> Result<Vec<String>, Error> {
    let new_msgs = build_update_client(
        dst_chain.clone(),
        src_chain.clone(),
        dst_client_id,
        src_chain.query_latest_height()?,
    )?;

    Ok(dst_chain.send_msgs(new_msgs)?)
}

/// Tests the integration of crates `relayer` plus `relayer-cli` against crate `ibc`. These tests
/// exercise various client methods (create, update, ForeignClient::new) using locally-running
/// instances of chains built using `MockChain`.
#[cfg(test)]
mod test {
    use std::str::FromStr;

    use ibc::ics24_host::identifier::ClientId;
    use ibc::Height;

    use crate::chain::mock::test_utils::get_basic_chain_config;
    use crate::chain::mock::MockChain;
    use crate::chain::runtime::ChainRuntime;
    use crate::foreign_client::{
        build_create_client_and_send, build_update_client_and_send, ForeignClient,
    };

    /// Basic test for the `build_create_client_and_send` method.
    #[test]
    fn create_client_and_send_method() {
        let a_cfg = get_basic_chain_config("chain_a");
        let b_cfg = get_basic_chain_config("chain_b");

        let (a_chain, _) = ChainRuntime::<MockChain>::spawn(a_cfg).unwrap();
        let (b_chain, _) = ChainRuntime::<MockChain>::spawn(b_cfg).unwrap();

        // Create the client on chain a
        let res = build_create_client_and_send(a_chain.clone(), b_chain.clone());
        assert!(
            res.is_ok(),
            "build_create_client_and_send failed (chain a) with error {:?}",
            res
        );

        // Create the client on chain b
        let res = build_create_client_and_send(b_chain.clone(), a_chain.clone());
        assert!(
            res.is_ok(),
            "build_create_client_and_send failed (chain b) with error {:?}",
            res
        );
    }

    /// Basic test for the `build_update_client_and_send` & `build_create_client_and_send` methods.
    #[test]
    fn update_client_and_send_method() {
        let a_cfg = get_basic_chain_config("chain_a");
        let b_cfg = get_basic_chain_config("chain_b");
        let mut a_client_id = ClientId::from_str("client_on_a_forb").unwrap();

        // The number of ping-pong iterations
        let num_iterations = 3;

        let (a_chain, _) = ChainRuntime::<MockChain>::spawn(a_cfg).unwrap();
        let (b_chain, _) = ChainRuntime::<MockChain>::spawn(b_cfg).unwrap();

        // This action should fail because no client exists (yet)
        let res = build_update_client_and_send(a_chain.clone(), b_chain.clone(), &a_client_id);
        assert!(
            res.is_err(),
            "build_update_client_and_send was supposed to fail (no client existed)"
        );

        // Remember b's height.
        let b_height_start = b_chain.query_latest_height().unwrap();

        // Create a client on chain a
        let res = build_create_client_and_send(a_chain.clone(), b_chain.clone());
        assert!(
            res.is_ok(),
            "build_create_client_and_send failed (chain a) with error {:?}",
            res
        );
        a_client_id = res.unwrap();

        // This should fail because the client on chain a already has the latest headers. Chain b,
        // the source chain for the client on a, is at the same height where it was when the client
        // was created, so an update should fail here.
        let res = build_update_client_and_send(a_chain.clone(), b_chain.clone(), &a_client_id);
        assert!(
            res.is_err(),
            "build_update_client_and_send was supposed to fail",
        );

        // Remember b's height.
        let b_height_last = b_chain.query_latest_height().unwrap();
        assert_eq!(b_height_last, b_height_start);

        // Create a client on chain b
        let res = build_create_client_and_send(b_chain.clone(), a_chain.clone());
        assert!(
            res.is_ok(),
            "build_create_client_and_send failed (chain b) with error {:?}",
            res
        );

        // Remember the id of the client we created on chain b
        let b_client_id = res.unwrap();

        // Chain b should have advanced
        let mut b_height_last = b_chain.query_latest_height().unwrap();
        assert_eq!(b_height_last, b_height_start.increment());

        // Remember the current height of chain a
        let mut a_height_last = a_chain.query_latest_height().unwrap();

        // Now we can update both clients -- a ping pong, similar to ICS18 `client_update_ping_pong`
        for _i in 1..num_iterations {
            let res = build_update_client_and_send(a_chain.clone(), b_chain.clone(), &a_client_id);
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
            let res = build_update_client_and_send(b_chain.clone(), a_chain.clone(), &b_client_id);
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

        let (a_chain, _) = ChainRuntime::<MockChain>::spawn(a_cfg).unwrap();
        let (b_chain, _) = ChainRuntime::<MockChain>::spawn(b_cfg).unwrap();

        // Instantiate the foreign clients on the two chains.
        let res_client_on_a = ForeignClient::new(a_chain.clone(), b_chain.clone());
        assert!(
            res_client_on_a.is_ok(),
            "Client creation (on chain a) failed with error: {:?}",
            res_client_on_a
        );

        let client_on_a = res_client_on_a.unwrap();
        assert!(
            client_on_a.id().is_some(),
            "Client identifier for client on chain a was not set!"
        );
        let a_client = client_on_a.id.unwrap();

        let res_client_on_b = ForeignClient::new(b_chain.clone(), a_chain.clone());
        assert!(
            res_client_on_b.is_ok(),
            "Client creation (on chain a) failed with error: {:?}",
            res_client_on_b
        );
        let client_on_b = res_client_on_b.unwrap();
        assert!(
            client_on_b.id().is_some(),
            "Client identifier for client on chain b was not set!"
        );
        let b_client = client_on_b.id.unwrap();

        // Now that the clients exists, we should be able to query its state
        let b_client_state = b_chain.query_client_state(&b_client, Height::default());
        assert!(
            b_client_state.is_ok(),
            "Client query (on chain b) failed with error: {:?}",
            b_client_state
        );

        let a_client_state = a_chain.query_client_state(&a_client, Height::default());
        assert!(
            a_client_state.is_ok(),
            "Client query (on chain a) failed with error: {:?}",
            a_client_state
        );
    }

    /// Tests for `ForeignClient::update()`.
    #[test]
    fn foreign_client_update() {
        let a_cfg = get_basic_chain_config("chain_a");
        let b_cfg = get_basic_chain_config("chain_b");
        let mut _a_client_id = ClientId::from_str("client_on_a_forb").unwrap();
        let mut _b_client_id = ClientId::from_str("client_on_b_fora").unwrap();

        let (a_chain, _) = ChainRuntime::<MockChain>::spawn(a_cfg).unwrap();
        let (b_chain, _) = ChainRuntime::<MockChain>::spawn(b_cfg).unwrap();

        // Instantiate the foreign clients on the two chains.
        let client_on_a_res = ForeignClient::new(a_chain.clone(), b_chain.clone());
        assert!(
            client_on_a_res.is_ok(),
            "Client creation (on chain a) failed with error: {:?}",
            client_on_a_res
        );
        let client_on_a = client_on_a_res.unwrap();

        let client_on_b_res = ForeignClient::new(b_chain.clone(), a_chain.clone());
        assert!(
            client_on_b_res.is_ok(),
            "Client creation (on chain a) failed with error: {:?}",
            client_on_b_res
        );
        let client_on_b = client_on_b_res.unwrap();

        let num_iterations = 5;

        let mut b_height_start = b_chain.query_latest_height().unwrap();
        let mut a_height_start = a_chain.query_latest_height().unwrap();

        // Update each client
        for _i in 1..num_iterations {
            let res = client_on_a.update();
            assert!(res.is_ok(), "Client update for chain a failed {:?}", res);

            // Basic check that the height of the chain advanced
            let a_height_current = a_chain.query_latest_height().unwrap();
            a_height_start = a_height_start.increment();
            assert_eq!(
                a_height_start, a_height_current,
                "after client update, chain a did not advance"
            );

            let res = client_on_b.update();
            assert!(res.is_ok(), "Client update for chain b failed {:?}", res);

            // Basic check that the height of the chain advanced
            let b_height_current = b_chain.query_latest_height().unwrap();
            b_height_start = b_height_start.increment();
            assert_eq!(
                b_height_start, b_height_current,
                "after client update, chain b did not advance"
            );
        }
    }
}
