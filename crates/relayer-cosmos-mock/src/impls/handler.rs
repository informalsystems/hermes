use crate::contexts::chain::MockCosmosChain;
use crate::traits::handler::ChainHandler;
use crate::types::error::Error;
use crate::util::conversion::convert_tm_to_ics_merkle_proof;
use crate::util::dummy::genesis_app_state;
use crate::util::mutex::MutexUtil;

use basecoin_app::modules::types::IdentifiedModule;
use basecoin_store::context::ProvableStore;
use basecoin_store::context::Store;
use basecoin_store::utils::SharedRwExt;

use ibc::core::events::IbcEvent;
use ibc::core::ics23_commitment::commitment::CommitmentProofBytes;
use ibc::core::ics24_host::path::Path;
use ibc::hosts::tendermint::IBC_QUERY_PATH;
use ibc::Any;
use ibc::Height;

use tendermint::block::Height as TmHeight;
use tendermint::time::Time;
use tendermint::v0_37::abci::request::InitChain;
use tendermint::v0_37::abci::request::Query;
use tendermint::v0_37::abci::Request as AbciRequest;
use tendermint::v0_37::abci::Response as AbciResponse;
use tendermint_testgen::consensus::default_consensus_params;
use tower::Service;

use async_trait::async_trait;
use std::time::Duration;

#[async_trait]
impl ChainHandler for MockCosmosChain {
    /// Initialize the chain with the app state.
    async fn init(&self) {
        let app_state = serde_json::to_vec(&genesis_app_state()).expect("infallible serialization");

        let request = InitChain {
            time: Time::now(),
            chain_id: self.chain_id.to_string(),
            consensus_params: default_consensus_params(),
            validators: vec![],
            app_state_bytes: app_state.into(),
            initial_height: TmHeight::from(1_u8),
        };

        let mut app = self.app.clone();

        app.call(AbciRequest::InitChain(request))
            .await
            .expect("failed to initialize chain");

        // Generates the genesis block
        self.grow_blocks();
    }

    async fn begin_block(&self) {
        let last_block = self.blocks.acquire_mutex().last().unwrap().clone();

        let mut events = Vec::new();

        let mut modules = self.app.modules.write_access();

        for IdentifiedModule { id: _, module } in modules.iter_mut() {
            let event = module.begin_block(&last_block.signed_header.header);
            events.extend(event);
        }
    }

    /// Commits the chain state.
    async fn commit(&self) {
        let mut modules = self.app.modules.write_access();

        for IdentifiedModule { id, module } in modules.iter_mut() {
            module
                .store_mut()
                .commit()
                .expect("failed to commit to state");

            let mut state = self.app.store.write_access();

            state
                .set(id.clone().into(), module.store().root_hash())
                .expect("failed to update sub-store commitment");
        }

        let mut state = self.app.store.write_access();

        state.commit().expect("failed to commit to state");

        self.grow_blocks();
    }

    async fn run(&self) {
        self.init().await;

        loop {
            self.begin_block().await;

            tokio::time::sleep(Duration::from_millis(100)).await;

            self.commit().await;
        }
    }

    async fn submit_messages(&self, msgs: Vec<Any>) -> Result<Vec<Vec<IbcEvent>>, Error> {
        let mut events = Vec::new();

        for msg in msgs {
            let ibc_events = self.app.ibc().process_message(msg)?;

            events.push(ibc_events);
        }

        Ok(events)
    }

    /// Queries the mock chain for the given path and height.
    async fn query(
        &self,
        path: impl Into<Path> + Send,
        height: &Height,
    ) -> Result<(Vec<u8>, CommitmentProofBytes), Error> {
        let request = Query {
            path: IBC_QUERY_PATH.to_string(),
            data: path.into().to_string().into_bytes().into(),
            height: TmHeight::try_from(height.revision_height()).unwrap(),
            prove: true,
        };

        let mut app = self.app.clone();

        let response = match app
            .call(AbciRequest::Query(request))
            .await
            .map_err(Error::source)?
        {
            AbciResponse::Query(res) => res,
            _ => panic!("unexpected response from query"),
        };

        let proof = match response.proof {
            Some(proof) => proof,
            None => return Err(Error::empty("proof")),
        };

        let merkle_proof = convert_tm_to_ics_merkle_proof(&proof)?;

        let commitment_proof = merkle_proof.try_into().map_err(Error::source)?;

        Ok((response.value.into(), commitment_proof))
    }
}
