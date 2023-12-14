use eyre::eyre;
use http::Uri;
use ibc_proto::{
    cosmos::gov::v1beta1::{
        query_client::QueryClient,
        QueryProposalRequest,
    },
    ibc::core::client::v1::{
        MsgIbcSoftwareUpgrade,
        UpgradeProposal,
    },
};
use ibc_relayer::{
    config::default::max_grpc_decoding_size,
    error::Error as RelayerError,
};
use prost::Message;

use crate::{
    chain::{
        cli::upgrade::vote_proposal,
        driver::ChainDriver,
    },
    error::Error,
    prelude::handle_generic_error,
    types::tagged::*,
};

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

    client = client.max_decoding_message_size(max_grpc_decoding_size().get_bytes() as usize);

    let request = tonic::Request::new(QueryProposalRequest { proposal_id });

    let response = client
        .proposal(request)
        .await
        .map(|r| r.into_inner())
        .map_err(|e| RelayerError::grpc_status(e, "query_upgrade_proposal_height".to_owned()))?;

    // Querying for a balance might fail, i.e. if the account doesn't actually exist
    let proposal = response
        .proposal
        .ok_or_else(|| RelayerError::empty_query_account(proposal_id.to_string()))?;

    let proposal_content = proposal
        .content
        .ok_or_else(|| eyre!("failed to retrieve content of Proposal"))?;

    let height = match proposal_content.type_url.as_str() {
        "/ibc.core.client.v1.MsgIBCSoftwareUpgrade" => {
            let upgrade_plan = MsgIbcSoftwareUpgrade::decode(&proposal_content.value as &[u8])
                .map_err(handle_generic_error)?;

            let plan = upgrade_plan
                .plan
                .ok_or_else(|| eyre!("failed to plan from MsgIbcSoftwareUpgrade"))?;

            plan.height as u64
        }
        "/ibc.core.client.v1.UpgradeProposal" => {
            let upgrade_plan = UpgradeProposal::decode(&proposal_content.value as &[u8])
                .map_err(handle_generic_error)?;

            let plan = upgrade_plan
                .plan
                .ok_or_else(|| eyre!("failed to plan from MsgIbcSoftwareUpgrade"))?;

            plan.height as u64
        }
        _ => {
            return Err(Error::incorrect_proposal_type_url(
                proposal_content.type_url,
            ))
        }
    };

    Ok(height)
}
