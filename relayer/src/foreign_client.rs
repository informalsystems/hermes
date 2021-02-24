use prost_types::Any;
use std::{thread, time::Duration};
use thiserror::Error;
use tracing::{error, info};

use ibc::events::IBCEvent;
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
    /// so we may be using the default value temporarily.
    pub id: ClientId,

    /// A handle to the chain hosting this client, i.e., destination chain.
    pub dst_chain: Box<dyn ChainHandle>,

    /// A handle to the chain whose headers this client is verifying, aka the source chain.
    pub src_chain: Box<dyn ChainHandle>,
}

impl ForeignClient {
    /// Creates a new foreign client on `dst_chain`. Blocks until the client is created, or
    /// an error occurs.
    /// Post-condition: `dst_chain` hosts an IBC client for `src_chain`.
    pub fn new(
        dst_chain: Box<dyn ChainHandle>,
        src_chain: Box<dyn ChainHandle>,
    ) -> Result<ForeignClient, ForeignClientError> {
        // Sanity check
        if src_chain.id().eq(&dst_chain.id()) {
            return Err(ForeignClientError::ClientCreate(format!(
                "the source ({}) and destination ({}) chains must be different",
                src_chain.id(),
                dst_chain.id(),
            )));
        }

        let mut client = ForeignClient {
            id: ClientId::default(),
            dst_chain: dst_chain.clone(),
            src_chain: src_chain.clone(),
        };

        client.create()?;

        Ok(client)
    }
    /// Returns a handle to the chain hosting this client.
    pub fn dst_chain(&self) -> Box<dyn ChainHandle> {
        self.dst_chain.clone()
    }

    /// Returns a handle to the chain whose headers this client is sourcing (the source chain).
    pub fn src_chain(&self) -> Box<dyn ChainHandle> {
        self.src_chain.clone()
    }

    pub fn id(&self) -> &ClientId {
        &self.id
    }

    /// Lower-level interface for preparing a message to create a client.
    pub fn build_create_client(&self) -> Result<MsgCreateAnyClient, ForeignClientError> {
        // Get signer
        let signer = self.dst_chain.get_signer().map_err(|e| {
            ForeignClientError::ClientCreate(format!(
                "failed while fetching the destination chain ({}) signer: {}",
                self.dst_chain.id(),
                e
            ))
        })?;

        // Build client create message with the data from source chain at latest height.
        let latest_height = self.src_chain.query_latest_height().map_err(|e| {
            ForeignClientError::ClientCreate(format!(
                "failed while querying src chain ({}) for latest height: {}",
                self.src_chain.id(),
                e
            ))
        })?;

        let client_state = self
            .src_chain
            .build_client_state(latest_height)
            .map_err(|e| {
                ForeignClientError::ClientCreate(format!(
                    "failed while building client state from src chain ({}) with error: {}",
                    self.src_chain.id(),
                    e
                ))
            })?
            .wrap_any();

        let consensus_state = self.src_chain
            .build_consensus_state(latest_height)
            .map_err(|e| ForeignClientError::ClientCreate(format!("failed while building client consensus state from src chain ({}) with error: {}", self.src_chain.id(), e)))?
            .wrap_any();

        //TODO Get acct_prefix
        let msg = MsgCreateAnyClient::new(client_state, consensus_state, signer).map_err(|e| {
            ForeignClientError::ClientCreate(format!(
                "failed while building the create client message: {}",
                e
            ))
        })?;

        Ok(msg)
    }

    /// Returns the identifier of the newly created client.
    pub fn build_create_client_and_send(&self) -> Result<IBCEvent, ForeignClientError> {
        let new_msg = self.build_create_client()?;

        let res = self
            .dst_chain
            .send_msgs(vec![new_msg.to_any::<RawMsgCreateClient>()])
            .map_err(|e| {
                ForeignClientError::ClientCreate(format!(
                    "failed sending message to dst chain ({}) with err: {}",
                    self.dst_chain.id(),
                    e
                ))
            })?;

        assert!(!res.is_empty());
        Ok(res[0].clone())
    }

    /// Sends the client creation transaction & subsequently sets the id of this ForeignClient
    fn create(&mut self) -> Result<(), ForeignClientError> {
        let done = '\u{1F36D}';

        match self.build_create_client_and_send() {
            Err(e) => {
                error!("Failed CreateClient {:?}: {}", self.dst_chain.id(), e);
                return Err(ForeignClientError::ClientCreate(format!(
                    "Create client failed ({:?})",
                    e
                )));
            }
            Ok(event) => {
                self.id = extract_client_id(&event)?.clone();
                println!("{}  {} => {:?}\n", done, self.dst_chain.id(), event);
            }
        }
        Ok(())
    }

    pub fn build_update_client(
        &self,
        target_height: Height,
    ) -> Result<Vec<Any>, ForeignClientError> {
        // Wait for source chain to reach `target_height`
        while self.src_chain().query_latest_height().map_err(|e| {
            ForeignClientError::ClientUpdate(format!(
                "failed fetching src chain latest height with error: {}",
                e
            ))
        })? < target_height
        {
            thread::sleep(Duration::from_millis(100))
        }

        // Get the latest trusted height from the client state on destination.
        let trusted_height = self
            .dst_chain()
            .query_client_state(&self.id, Height::default())
            .map_err(|e| {
                ForeignClientError::ClientUpdate(format!(
                    "failed querying client state on dst chain {} with error: {}",
                    self.id, e
                ))
            })?
            .latest_height();

        let header = self
            .src_chain()
            .build_header(trusted_height, target_height)
            .map_err(|e| {
                ForeignClientError::ClientUpdate(format!(
                    "failed building header with error: {}",
                    e
                ))
            })?
            .wrap_any();

        let signer = self.dst_chain().get_signer().map_err(|e| {
            ForeignClientError::ClientUpdate(format!(
                "failed getting signer for dst chain ({}) with error: {}",
                self.dst_chain.id(),
                e
            ))
        })?;
        let new_msg = MsgUpdateAnyClient {
            client_id: self.id.clone(),
            header,
            signer,
        };

        Ok(vec![new_msg.to_any::<RawMsgUpdateClient>()])
    }

    pub fn build_update_client_and_send(&self) -> Result<IBCEvent, ForeignClientError> {
        let h = self.src_chain.query_latest_height().map_err(|e| {
            ForeignClientError::ClientUpdate(format!(
                "failed while querying src chain ({}) for latest height: {}",
                self.src_chain.id(),
                e
            ))
        })?;
        let new_msgs = self.build_update_client(h)?;

        let mut events = self.dst_chain().send_msgs(new_msgs).map_err(|e| {
            ForeignClientError::ClientUpdate(format!(
                "failed sending message to dst chain ({}) with err: {}",
                self.dst_chain.id(),
                e
            ))
        })?;

        assert!(!events.is_empty());
        Ok(events.pop().unwrap())
    }

    /// Attempts to update a client using header from the latest height of its source chain.
    pub fn update(&self) -> Result<(), ForeignClientError> {
        let res = self.build_update_client_and_send().map_err(|e| {
            ForeignClientError::ClientUpdate(format!("build_create_client_and_send {:?}", e))
        })?;

        info!(
            "Client id {:?} on {:?} updated with return message {:?}\n",
            self.id,
            self.dst_chain.id(),
            res
        );

        Ok(())
    }
}

pub fn extract_client_id(event: &IBCEvent) -> Result<&ClientId, ForeignClientError> {
    match event {
        IBCEvent::CreateClient(ev) => Ok(ev.client_id()),
        IBCEvent::UpdateClient(ev) => Ok(ev.client_id()),
        _ => Err(ForeignClientError::ClientCreate(
            "cannot extract client_id from result".to_string(),
        )),
    }
}

/// Tests the integration of crates `relayer` plus `relayer-cli` against crate `ibc`. These tests
/// exercise various client methods (create, update, ForeignClient::new) using locally-running
/// instances of chains built using `MockChain`.
#[cfg(test)]
mod test {
    use std::str::FromStr;

    use ibc::events::IBCEvent;
    use ibc::ics24_host::identifier::ClientId;
    use ibc::Height;

    use crate::chain::mock::test_utils::get_basic_chain_config;
    use crate::chain::mock::MockChain;
    use crate::chain::runtime::ChainRuntime;
    use crate::foreign_client::ForeignClient;

    /// Basic test for the `build_create_client_and_send` method.
    #[test]
    fn create_client_and_send_method() {
        let a_cfg = get_basic_chain_config("chain_a");
        let b_cfg = get_basic_chain_config("chain_b");

        let (a_chain, _) = ChainRuntime::<MockChain>::spawn(a_cfg).unwrap();
        let (b_chain, _) = ChainRuntime::<MockChain>::spawn(b_cfg).unwrap();
        let a_client = ForeignClient {
            id: Default::default(),
            dst_chain: a_chain.clone(),
            src_chain: b_chain.clone(),
        };

        let b_client = ForeignClient {
            id: Default::default(),
            dst_chain: b_chain,
            src_chain: a_chain,
        };

        // Create the client on chain a
        let res = a_client.build_create_client_and_send();
        assert!(
            res.is_ok(),
            "build_create_client_and_send failed (chain a) with error {:?}",
            res
        );
        assert!(matches!(res.unwrap(), IBCEvent::CreateClient(_)));

        // Create the client on chain b
        let res = b_client.build_create_client_and_send();
        assert!(
            res.is_ok(),
            "build_create_client_and_send failed (chain b) with error {:?}",
            res
        );
        assert!(matches!(res.unwrap(), IBCEvent::CreateClient(_)));
    }

    /// Basic test for the `build_update_client_and_send` & `build_create_client_and_send` methods.
    #[test]
    fn update_client_and_send_method() {
        let a_cfg = get_basic_chain_config("chain_a");
        let b_cfg = get_basic_chain_config("chain_b");
        let a_client_id = ClientId::from_str("client_on_a_forb").unwrap();

        // The number of ping-pong iterations
        let num_iterations = 3;

        let (a_chain, _) = ChainRuntime::<MockChain>::spawn(a_cfg).unwrap();
        let (b_chain, _) = ChainRuntime::<MockChain>::spawn(b_cfg).unwrap();
        let mut a_client = ForeignClient {
            id: a_client_id,
            dst_chain: a_chain.clone(),
            src_chain: b_chain.clone(),
        };

        let mut b_client = ForeignClient {
            id: Default::default(),
            dst_chain: b_chain.clone(),
            src_chain: a_chain.clone(),
        };

        // This action should fail because no client exists (yet)
        let res = a_client.build_update_client_and_send();
        assert!(
            res.is_err(),
            "build_update_client_and_send was supposed to fail (no client existed)"
        );

        // Remember b's height.
        let b_height_start = b_chain.clone().query_latest_height().unwrap();

        // Create a client on chain a
        let res = a_client.create();
        assert!(
            res.is_ok(),
            "build_create_client_and_send failed (chain a) with error {:?}",
            res
        );

        // TODO: optionally add return events from `create` and assert on the event type, e.g.:
        //      assert!(matches!(res.as_ref().unwrap(), IBCEvent::CreateClient(_)));
        //      let a_client_id = extract_client_id(&res.unwrap()).unwrap().clone();

        // This should fail because the client on chain a already has the latest headers. Chain b,
        // the source chain for the client on a, is at the same height where it was when the client
        // was created, so an update should fail here.
        let res = a_client.build_update_client_and_send();
        assert!(
            res.is_err(),
            "build_update_client_and_send was supposed to fail",
        );

        // Remember b's height.
        let b_height_last = b_chain.query_latest_height().unwrap();
        assert_eq!(b_height_last, b_height_start);

        // Create a client on chain b
        let res = b_client.create();
        assert!(
            res.is_ok(),
            "build_create_client_and_send failed (chain b) with error {:?}",
            res
        );
        // TODO: assert return events
        //  assert!(matches!(res.as_ref().unwrap(), IBCEvent::CreateClient(_)));

        // Chain b should have advanced
        let mut b_height_last = b_chain.query_latest_height().unwrap();
        assert_eq!(b_height_last, b_height_start.increment());

        // Remember the current height of chain a
        let mut a_height_last = a_chain.query_latest_height().unwrap();

        // Now we can update both clients -- a ping pong, similar to ICS18 `client_update_ping_pong`
        for _i in 1..num_iterations {
            let res = a_client.build_update_client_and_send();
            assert!(
                res.is_ok(),
                "build_update_client_and_send failed (chain a) with error: {:?}",
                res
            );
            assert!(matches!(res.as_ref().unwrap(), IBCEvent::UpdateClient(_)));

            let a_height_current = a_chain.query_latest_height().unwrap();
            a_height_last = a_height_last.increment();
            assert_eq!(
                a_height_last, a_height_current,
                "after client update, chain a did not advance"
            );

            // And also update the client on chain b.
            let res = b_client.build_update_client_and_send();
            assert!(
                res.is_ok(),
                "build_update_client_and_send failed (chain b) with error: {:?}",
                res
            );
            assert!(matches!(res.as_ref().unwrap(), IBCEvent::UpdateClient(_)));

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
        let a_client = client_on_a.id;

        let res_client_on_b = ForeignClient::new(b_chain.clone(), a_chain.clone());
        assert!(
            res_client_on_b.is_ok(),
            "Client creation (on chain a) failed with error: {:?}",
            res_client_on_b
        );
        let client_on_b = res_client_on_b.unwrap();
        let b_client = client_on_b.id;

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
