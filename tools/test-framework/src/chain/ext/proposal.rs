use eyre::eyre;
use http::Uri;
use ibc_relayer::config::default::max_grpc_decoding_size;
use prost::Message;

use ibc_proto::cosmos::gov::v1beta1::{query_client::QueryClient, QueryProposalRequest};
use ibc_proto::ibc::core::client::v1::{MsgIbcSoftwareUpgrade, UpgradeProposal};
use ibc_relayer::error::Error as RelayerError;

use crate::chain::cli::upgrade::{submit_gov_proposal, vote_proposal};
use crate::chain::driver::ChainDriver;
use crate::error::Error;
use crate::prelude::{handle_generic_error, TaggedChainDriverExt};
use crate::types::tagged::*;

use super::bootstrap::ChainBootstrapMethodsExt;

pub trait ChainProposalMethodsExt {
    fn query_upgrade_proposal_height(
        &self,
        grpc_address: &Uri,
        proposal_id: u64,
    ) -> Result<u64, Error>;

    fn vote_proposal(&self, fees: &str) -> Result<(), Error>;

    fn initialise_channel_upgrade(
        &self,
        port_id: &str,
        channel_id: &str,
        ordering: &str,
        connection_hops: &str,
        version: &str,
        signer: &str,
    ) -> Result<(), Error>;
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

    fn initialise_channel_upgrade(
        &self,
        port_id: &str,
        channel_id: &str,
        ordering: &str,
        connection_hops: &str,
        version: &str,
        signer: &str,
    ) -> Result<(), Error> {
        let gov_address = self.query_auth_module("gov")?;
        let channel_upgrade_proposal = create_channel_upgrade_proposal(
            self.value(),
            port_id,
            channel_id,
            ordering,
            connection_hops,
            version,
            &gov_address,
        )?;
        submit_gov_proposal(
            self.value().chain_id.as_str(),
            &self.value().command_path,
            &self.value().home_path,
            &self.value().rpc_listen_address(),
            signer,
            &channel_upgrade_proposal,
        )?;

        self.value().assert_proposal_status(
            self.value().chain_id.as_str(),
            &self.value().command_path,
            &self.value().home_path,
            &self.value().rpc_listen_address(),
            "PROPOSAL_STATUS_VOTING_PERIOD",
            "1",
        )?;

        vote_proposal(
            self.value().chain_id.as_str(),
            &self.value().command_path,
            &self.value().home_path,
            &self.value().rpc_listen_address(),
            "1200stake",
        )?;

        self.value().assert_proposal_status(
            self.value().chain_id.as_str(),
            &self.value().command_path,
            &self.value().home_path,
            &self.value().rpc_listen_address(),
            "PROPOSAL_STATUS_PASSED",
            "1",
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

fn create_channel_upgrade_proposal(
    chain_driver: &ChainDriver,
    port_id: &str,
    channel_id: &str,
    ordering: &str,
    connection_hops: &str,
    version: &str,
    gov_address: &str,
) -> Result<String, Error> {
    let raw_proposal = r#"
    {
        "messages": [
            {
              "@type": "/ibc.core.channel.v1.MsgChannelUpgradeInit",
              "port_id": "{port_id}",
              "channel_id": "{channel_id}",
              "fields": {
                "ordering": "{ordering}",
                "connection_hops": ["{connection_hops}"],
                "version": {version}
              },
              "signer":{signer}
            }
          ],
        "deposit": "10000001stake",
        "title": "Channel upgrade",
        "summary": "Upgrade channel version",
        "expedited": false
    }"#;

    let proposal = raw_proposal.replace("{port_id}", port_id);
    let proposal = proposal.replace("{channel_id}", channel_id);
    let proposal = proposal.replace("{ordering}", ordering);
    let proposal = proposal.replace("{connection_hops}", connection_hops);
    let proposal = proposal.replace("{version}", version);
    let proposal = proposal.replace("{signer}", gov_address);

    chain_driver.write_file("channel_upgrade_proposal.json", &proposal)?;
    Ok("channel_upgrade_proposal.json".to_owned())
}
