use http::Uri;

use crate::chain::cli::proposal::{deposit_proposal, vote_proposal};
use crate::chain::cli::upgrade::query_upgrade_proposal_height;
use crate::chain::driver::ChainDriver;
use crate::error::Error;
use crate::types::tagged::*;

pub trait ChainProposalMethodsExt {
    fn query_upgrade_proposal_height(
        &self,
        grpc_address: &Uri,
        proposal_id: u64,
    ) -> Result<u64, Error>;

    fn vote_proposal(&self, proposal_id: &str, fees: &str) -> Result<(), Error>;

    fn deposit_proposal(&self, proposal_id: &str, amount: &str) -> Result<(), Error>;
}

impl<'a, Chain: Send> ChainProposalMethodsExt for MonoTagged<Chain, &'a ChainDriver> {
    fn query_upgrade_proposal_height(
        &self,
        grpc_address: &Uri,
        proposal_id: u64,
    ) -> Result<u64, Error> {
        self.value()
            .query_upgrade_proposal_height(grpc_address, proposal_id)
    }

    fn vote_proposal(&self, proposal_id: &str, fees: &str) -> Result<(), Error> {
        self.value().vote_proposal(proposal_id, fees)
    }

    fn deposit_proposal(&self, proposal_id: &str, amount: &str) -> Result<(), Error> {
        self.value().deposit_proposal(proposal_id, amount)
    }
}

impl ChainProposalMethodsExt for ChainDriver {
    fn query_upgrade_proposal_height(
        &self,
        grpc_address: &Uri,
        proposal_id: u64,
    ) -> Result<u64, Error> {
        self.runtime
            .block_on(query_upgrade_proposal_height(grpc_address, proposal_id))
    }

    fn vote_proposal(&self, proposal_id: &str, fees: &str) -> Result<(), Error> {
        vote_proposal(self, proposal_id, fees)
    }

    fn deposit_proposal(&self, proposal_id: &str, amount: &str) -> Result<(), Error> {
        deposit_proposal(self, proposal_id, amount)
    }
}
