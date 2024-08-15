use http::Uri;

use crate::chain::cli::proposal::{deposit_proposal, submit_gov_proposal, vote_proposal};
use crate::chain::cli::upgrade::query_upgrade_proposal_height;
use crate::chain::driver::ChainDriver;
use crate::error::Error;
use crate::prelude::TaggedChainDriverExt;
use crate::types::tagged::*;
use crate::util::proposal_status::ProposalStatus;

use super::bootstrap::ChainBootstrapMethodsExt;

pub trait ChainProposalMethodsExt {
    fn query_upgrade_proposal_height(
        &self,
        grpc_address: &Uri,
        proposal_id: u64,
    ) -> Result<u64, Error>;

    fn vote_proposal(&self, fees: &str, proposal_id: &str) -> Result<(), Error>;

    fn deposit_proposal(
        &self,
        amount: &str,
        proposal_id: &str,
        fees: &str,
        gas: &str,
    ) -> Result<(), Error>;
}

pub trait ChannelProposalMethodsExt {
    fn initialise_channel_upgrade(
        &self,
        port_id: &str,
        channel_id: &str,
        ordering: &str,
        connection_hops: &str,
        version: &str,
        signer: &str,
        proposal_id: &str,
    ) -> Result<(), Error>;

    fn update_channel_params(
        &self,
        timestamp: u64,
        signer: &str,
        proposal_id: &str,
    ) -> Result<(), Error>;
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

    fn deposit_proposal(
        &self,
        amount: &str,
        proposal_id: &str,
        fees: &str,
        gas: &str,
    ) -> Result<(), Error> {
        self.value()
            .deposit_proposal(amount, proposal_id, fees, gas)
    }
}

impl<'a, Chain: Send> ChannelProposalMethodsExt for MonoTagged<Chain, &'a ChainDriver> {
    fn initialise_channel_upgrade(
        &self,
        port_id: &str,
        channel_id: &str,
        ordering: &str,
        connection_hops: &str,
        version: &str,
        signer: &str,
        proposal_id: &str,
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

        self.value()
            .assert_proposal_status(ProposalStatus::VotingPeriod, proposal_id)?;

        self.value().vote_proposal(proposal_id, "1200stake")?;

        self.value()
            .assert_proposal_status(ProposalStatus::Passed, proposal_id)?;

        Ok(())
    }

    // The timestamp is in nanoseconds
    fn update_channel_params(
        &self,
        timestamp: u64,
        signer: &str,
        proposal_id: &str,
    ) -> Result<(), Error> {
        let gov_address = self.query_auth_module("gov")?;
        let channel_update_params_proposal =
            create_channel_update_params_proposal(self.value(), timestamp, &gov_address)?;
        submit_gov_proposal(
            self.value().chain_id.as_str(),
            &self.value().command_path,
            &self.value().home_path,
            &self.value().rpc_listen_address(),
            signer,
            &channel_update_params_proposal,
        )?;

        self.value()
            .assert_proposal_status(ProposalStatus::VotingPeriod, proposal_id)?;

        self.value().vote_proposal(proposal_id, "1200stake")?;

        self.value()
            .assert_proposal_status(ProposalStatus::Passed, proposal_id)?;

        Ok(())
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

    fn deposit_proposal(
        &self,
        amount: &str,
        proposal_id: &str,
        fees: &str,
        gas: &str,
    ) -> Result<(), Error> {
        deposit_proposal(self, amount, proposal_id, fees, gas)
    }
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
              "signer":"{signer}"
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

fn create_channel_update_params_proposal(
    chain_driver: &ChainDriver,
    timestamp: u64,
    gov_address: &str,
) -> Result<String, Error> {
    let raw_proposal = r#"
    {
        "messages": [
            {
              "@type": "/ibc.core.channel.v1.MsgUpdateParams",
              "params": {
                "upgrade_timeout": {
                    "timestamp": {timestamp}
                }
              },
              "authority":"{signer}"
            }
          ],
        "deposit": "10000001stake",
        "title": "Channel update params",
        "summary": "Update channel params",
        "expedited": false
    }"#;

    let proposal = raw_proposal.replace("{timestamp}", &timestamp.to_string());
    let proposal = proposal.replace("{signer}", gov_address);

    let output_file = "channel_update_params_proposal.json";

    chain_driver.write_file(output_file, &proposal)?;
    Ok(output_file.to_owned())
}
