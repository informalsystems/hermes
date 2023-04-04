use eyre::eyre;
use http::Uri;
use prost::Message;

use ibc_proto::cosmos::gov::v1beta1::{query_client::QueryClient, QueryProposalRequest};
use ibc_proto::ibc::core::client::v1::UpgradeProposal;
use ibc_relayer::error::Error as RelayerError;

use crate::chain::cli::upgrade::vote_proposal;
use crate::chain::driver::ChainDriver;
use crate::error::Error;
use crate::prelude::handle_generic_error;
use crate::types::tagged::*;

pub trait ChainProposalMethodsExt {
    fn query_upgrade_proposal_height(
        &self,
        grpc_address: &Uri,
        proposal_id: u64,
    ) -> Result<u64, Error>;

    fn vote_proposal(&self, fees: &str) -> Result<(), Error>;
}

impl<'a, Chain: Send> ChainProposalMethodsExt for MonoTagged<Chain, &'a ChainDriver> {
    fn query_upgrade_proposal_height(
        &self,
        grpc_address: &Uri,
        proposal_id: u64,
    ) -> Result<u64, Error> {
        self.value()
            .runtime
            .block_on(query_upgrade_proposal_height(grpc_address, proposal_id))
    }

    fn vote_proposal(&self, fees: &str) -> Result<(), Error> {
        vote_proposal(
            self.value().chain_id.as_str(),
            &self.value().command_path,
            &self.value().home_path,
            &self.value().rpc_listen_address(),
            fees,
        )?;
        Ok(())
    }
}

/// Query the proposal with the given proposal_id, which is supposed to be an UpgradeProposal.
/// Extract the Plan from the UpgradeProposal and get the height at which the chain upgrades,
/// from the Plan.
pub async fn query_upgrade_proposal_height(
    grpc_address: &Uri,
    proposal_id: u64,
) -> Result<u64, Error> {
    let mut client = match QueryClient::connect(grpc_address.clone()).await {
        Ok(client) => client,
        Err(_) => {
            return Err(Error::query_client());
        }
    };

    let request = tonic::Request::new(QueryProposalRequest { proposal_id });

    let response = client
        .proposal(request)
        .await
        .map(|r| r.into_inner())
        .map_err(RelayerError::grpc_status)?;

    // Querying for a balance might fail, i.e. if the account doesn't actually exist
    let proposal = response
        .proposal
        .ok_or_else(|| RelayerError::empty_query_account(proposal_id.to_string()))?;

    let proposal_content = proposal
        .content
        .ok_or_else(|| eyre!("failed to retrieve content of Proposal"))?;

    if proposal_content.type_url != *"/ibc.core.client.v1.UpgradeProposal" {
        return Err(Error::incorrect_proposal_type_url(
            proposal_content.type_url,
        ));
    }

    let upgrade_plan =
        UpgradeProposal::decode(&proposal_content.value as &[u8]).map_err(handle_generic_error)?;

    let plan = upgrade_plan
        .plan
        .ok_or_else(|| eyre!("failed to plan from UpgradeProposal"))?;

    Ok(plan.height as u64)
}
