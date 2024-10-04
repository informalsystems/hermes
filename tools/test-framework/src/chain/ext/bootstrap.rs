use chrono::DateTime;
use chrono::Duration as ChronoDuration;
use chrono::Utc;
use core::str::FromStr;
use eyre::eyre;
use hdpath::StandardHDPath;
use serde_json as json;
use std::fs;
use std::path::PathBuf;
use std::str;
use std::time::Duration;
use tracing::debug;

use ibc_relayer::keyring::{Secp256k1KeyPair, SigningKeyPair};

use crate::chain::cli::bootstrap::{
    add_genesis_account, add_genesis_validator, add_wallet, collect_gen_txs, initialize,
    start_chain,
};
use crate::chain::cli::provider::{
    copy_validator_key_pair, create_consumer, query_consumer_genesis, query_gov_proposal,
    replace_genesis_state, update_consumer, validator_opt_in,
};
use crate::chain::cli::query::query_auth_module;
use crate::chain::driver::ChainDriver;
use crate::chain::exec::simple_exec;
use crate::error::{handle_generic_error, Error};
use crate::ibc::token::Token;
use crate::prelude::assert_eventually_succeed;
use crate::types::process::ChildProcess;
use crate::types::wallet::{Wallet, WalletAddress, WalletId};
use crate::util::proposal_status::ProposalStatus;

pub trait ChainBootstrapMethodsExt {
    /**
       Read the content at a file path relative to the chain home
       directory, and return the result as a string.

       This is not efficient but is sufficient for testing purposes.
    */
    fn read_file(&self, file_path: &str) -> Result<String, Error>;

    /**
       Write the string content to a file path relative to the chain home
       directory.

       This is not efficient but is sufficient for testing purposes.
    */
    fn write_file(&self, file_path: &str, content: &str) -> Result<(), Error>;

    /**
       Modify the Gaia chain config which is saved in toml format.
    */
    fn update_chain_config(
        &self,
        file: &str,
        cont: impl FnOnce(&mut toml::Value) -> Result<(), Error>,
    ) -> Result<(), Error>;

    /**
       Initialized the chain data stores.

       This is used by
       [`bootstrap_single_node`](crate::bootstrap::single::bootstrap_single_node).
    */
    fn initialize(&self) -> Result<(), Error>;

    /**
       Modify the Gaia genesis file.
    */
    fn update_genesis_file(
        &self,
        file: &str,
        cont: impl FnOnce(&mut serde_json::Value) -> Result<(), Error>,
    ) -> Result<(), Error>;

    /**
       Add a wallet with the given ID to the full node's keyring.
    */
    fn add_wallet(&self, wallet_id: &str) -> Result<Wallet, Error>;

    /**
       Add a wallet address to the genesis account list for an uninitialized
       full node.
    */
    fn add_genesis_account(&self, wallet: &WalletAddress, amounts: &[&Token]) -> Result<(), Error>;

    /**
       Add a wallet ID with the given stake amount to be the genesis validator
       for an uninitialized chain.
    */
    fn add_genesis_validator(&self, wallet_id: &WalletId, token: &Token) -> Result<(), Error>;

    /**
       Call `gaiad collect-gentxs` to generate the genesis transactions.
    */
    fn collect_gen_txs(&self) -> Result<(), Error>;

    /**
       Start a full node by running in the background `gaiad start`.

       Returns a [`ChildProcess`] that stops the full node process when the
       value is dropped.
    */
    fn start(&self) -> Result<ChildProcess, Error>;

    fn create_permisionless_consumer(
        &self,
        consumer_chain_id: &str,
        fees: &str,
    ) -> Result<String, Error>;

    fn validator_opt_in(&self, consumer_chain_id: &str, fees: &str) -> Result<(), Error>;

    fn update_consumer(
        &self,
        consumer_chain_id: &str,
        fees: &str,
        validator: &str,
    ) -> Result<(), Error>;

    /**
       Assert that the proposal is eventually in the desired state.
    */
    fn assert_proposal_status(
        &self,
        chain_id: &str,
        command_path: &str,
        home_path: &str,
        rpc_listen_address: &str,
        status: ProposalStatus,
        proposal_id: &str,
    ) -> Result<(), Error>;

    /**
       Query a consumer chain's genesis.
    */
    fn query_consumer_genesis(
        &self,
        consumer_chain_driver: &ChainDriver,
        consumer_chain_id: &str,
    ) -> Result<(), Error>;

    /**
       Replace genesis state.
    */
    fn replace_genesis_state(&self) -> Result<(), Error>;

    /**
       Copy validator key pair.
    */
    fn copy_validator_key_pair(&self, provider_chain_driver: &ChainDriver) -> Result<(), Error>;
}

impl ChainBootstrapMethodsExt for ChainDriver {
    fn read_file(&self, file_path: &str) -> Result<String, Error> {
        let full_path = PathBuf::from(&self.home_path).join(file_path);
        let res = fs::read_to_string(full_path)?;
        Ok(res)
    }

    fn write_file(&self, file_path: &str, content: &str) -> Result<(), Error> {
        let full_path = PathBuf::from(&self.home_path).join(file_path);
        let full_path_str = format!("{}", full_path.display());
        fs::write(full_path, content)?;
        debug!("created new file {:?}", full_path_str);
        Ok(())
    }

    fn update_chain_config(
        &self,
        file: &str,
        cont: impl FnOnce(&mut toml::Value) -> Result<(), Error>,
    ) -> Result<(), Error> {
        let config_path = format!("config/{file}");

        let config1 = self.read_file(&config_path)?;

        let mut config2 = toml::from_str(&config1).map_err(handle_generic_error)?;

        cont(&mut config2)?;

        let config3 = toml::to_string_pretty(&config2).map_err(handle_generic_error)?;

        self.write_file(&config_path, &config3)?;

        Ok(())
    }

    fn initialize(&self) -> Result<(), Error> {
        initialize(self.chain_id.as_str(), &self.command_path, &self.home_path)
    }

    fn update_genesis_file(
        &self,
        file: &str,
        cont: impl FnOnce(&mut serde_json::Value) -> Result<(), Error>,
    ) -> Result<(), Error> {
        let config1 = self.read_file(&format!("config/{file}"))?;

        let mut config2 = serde_json::from_str(&config1).map_err(handle_generic_error)?;

        cont(&mut config2)?;

        let config3 = serde_json::to_string_pretty(&config2).map_err(handle_generic_error)?;

        self.write_file("config/genesis.json", &config3)?;

        Ok(())
    }

    fn add_wallet(&self, wallet_id: &str) -> Result<Wallet, Error> {
        let seed_content = add_wallet(
            self.chain_id.as_str(),
            &self.command_path,
            &self.home_path,
            wallet_id,
        )?;

        let json_val: json::Value = json::from_str(&seed_content).map_err(handle_generic_error)?;

        let wallet_address = json_val
            .get("address")
            .ok_or_else(|| eyre!("expect address string field to be present in json result"))?
            .as_str()
            .ok_or_else(|| eyre!("expect address string field to be present in json result"))?
            .to_string();

        let seed_path = format!("{wallet_id}-seed.json");
        self.write_file(&seed_path, &seed_content)?;

        let hd_path = StandardHDPath::from_str(self.chain_type.hd_path())
            .map_err(|e| eyre!("failed to create StandardHDPath: {:?}", e))?;

        let key = Secp256k1KeyPair::from_seed_file(&seed_content, &hd_path)
            .map_err(handle_generic_error)?;

        Ok(Wallet::new(wallet_id.to_string(), wallet_address, key))
    }

    fn add_genesis_account(&self, wallet: &WalletAddress, amounts: &[&Token]) -> Result<(), Error> {
        let amounts_str = amounts.iter().map(|t| t.to_string()).collect::<Vec<_>>();
        let extra_args = self
            .chain_type
            .extra_add_genesis_account_args(&self.chain_id);

        add_genesis_account(
            self.chain_id.as_str(),
            &self.command_path,
            &self.home_path,
            &wallet.0,
            &amounts_str,
            &extra_args.iter().map(|s| s.as_ref()).collect::<Vec<_>>(),
        )
    }

    fn add_genesis_validator(&self, wallet_id: &WalletId, token: &Token) -> Result<(), Error> {
        add_genesis_validator(
            self.chain_id.as_str(),
            &self.command_path,
            &self.home_path,
            &wallet_id.0,
            &token.to_string(),
        )
    }

    fn collect_gen_txs(&self) -> Result<(), Error> {
        collect_gen_txs(self.chain_id.as_str(), &self.command_path, &self.home_path)
    }

    fn start(&self) -> Result<ChildProcess, Error> {
        let extra_start_args = self.chain_type.extra_start_args();

        start_chain(
            &self.command_path,
            &self.home_path,
            &self.rpc_listen_address(),
            &self.grpc_listen_address(),
            &extra_start_args
                .iter()
                .map(|s| s.as_ref())
                .collect::<Vec<_>>(),
        )
    }

    fn create_permisionless_consumer(
        &self,
        consumer_chain_id: &str,
        fees: &str,
    ) -> Result<String, Error> {
        let raw_proposal = r#"
        {
            "chain_id": "{consumer_chain_id}",
            "metadata": {
                "name": "consumer-1-metadata-name",
                "description":"consumer-1-metadata-description",
                "metadata": "consumer-1-metadata-metadata"
            },
            "initialization_parameters": {
                "initial_height": {
                    "revision_number": 0,
                    "revision_height": 1
                },
                "genesis_hash": "Z2VuX2hhc2g=",
                "binary_hash": "YmluX2hhc2g=",
                "spawn_time": "{spawn_time}",
                "unbonding_period": 1728000000000000,
                "ccv_timeout_period": 2419200000000000,
                "transfer_timeout_period": 1800000000000,
                "consumer_redistribution_fraction": "0.75",
                "blocks_per_distribution_transmission": 1000,
                "historical_entries": 10000,
                "distribution_transmission_channel": ""
            }
        }"#;
        let current_time: DateTime<Utc> = Utc::now();
        let future_time = current_time + ChronoDuration::seconds(30);
        let spawn_time = future_time.to_rfc3339();

        let proposal = raw_proposal.replace("{consumer_chain_id}", consumer_chain_id);
        let proposal = proposal.replace("{spawn_time}", &spawn_time);

        self.write_file("consumer_proposal.json", &proposal)?;

        create_consumer(
            self.chain_id.as_str(),
            &self.command_path,
            &self.home_path,
            &self.rpc_listen_address(),
            fees,
        )
    }

    fn validator_opt_in(&self, consumer_chain_id: &str, fees: &str) -> Result<(), Error> {
        let show_validator_output = simple_exec(
            "test",
            &self.command_path,
            &["comet", "show-validator", "--home", &self.home_path],
        )?;

        validator_opt_in(
            self.chain_id.as_str(),
            &self.command_path,
            &self.home_path,
            &self.rpc_listen_address(),
            fees,
            consumer_chain_id,
            &show_validator_output.stdout,
        )
    }

    fn update_consumer(
        &self,
        consumer_chain_id: &str,
        fees: &str,
        validator: &str,
    ) -> Result<(), Error> {
        let gov_address = query_auth_module(
            self.chain_id.as_str(),
            &self.command_path,
            &self.home_path,
            &self.rpc_listen_address(),
            "gov",
        )?;
        let res = simple_exec(
            self.chain_id.as_str(),
            "jq",
            &[
                "-r",
                ".genesis_time",
                &format!("{}/config/genesis.json", self.home_path),
            ],
        )?;
        let mut spawn_time = res.stdout;
        // Remove newline character
        spawn_time.pop();
        let raw_proposal = r#"
        {
            "consumer_id": "{consumer_chain_id}",
            "owner_address": "{validator}",
            "new_owner_address": "{gov_address}",
            "metadata": {
                "name": "consumer-1-metadata-name",
                "description":"consumer-1-metadata-description",
                "metadata": "consumer-1-metadata-metadata"
            }
        }"#;

        let proposal = raw_proposal.replace("{consumer_chain_id}", consumer_chain_id);
        let proposal = proposal.replace("{gov_address}", &gov_address);
        let proposal = proposal.replace("{validator}", validator);

        self.write_file("consumer_update_proposal.json", &proposal)?;

        update_consumer(
            self.chain_id.as_str(),
            &self.command_path,
            &self.home_path,
            &self.rpc_listen_address(),
            fees,
        )
    }

    fn assert_proposal_status(
        &self,
        chain_id: &str,
        command_path: &str,
        home_path: &str,
        rpc_listen_address: &str,
        status: ProposalStatus,
        proposal_id: &str,
    ) -> Result<(), Error> {
        assert_eventually_succeed(
            &format!("proposal `{}` status: {}", proposal_id, status.as_str()),
            10,
            Duration::from_secs(3),
            || match query_gov_proposal(
                chain_id,
                command_path,
                home_path,
                rpc_listen_address,
                proposal_id,
            ) {
                Ok(exec_output) => {
                    let json_res = json::from_str::<json::Value>(&exec_output.stdout)
                        .map_err(handle_generic_error)?;
                    // Cosmos SDK v0.50.1 outputs the status of the proposal using an integer code
                    let proposal_status: ProposalStatus = match json_res.get("proposal") {
                        Some(proposal_status) => proposal_status
                            .get("status")
                            .ok_or_else(|| eyre!("expected `status` field"))?
                            .try_into()?,
                        None => json_res
                            .get("status")
                            .ok_or_else(|| eyre!("expected `status` field"))?
                            .try_into()?,
                    };

                    if proposal_status == status {
                        Ok(())
                    } else {
                        Err(Error::generic(eyre!(
                            "proposal is not in `{}`. Proposal status: {}",
                            status.as_str(),
                            proposal_status.as_str()
                        )))
                    }
                }
                Err(e) => {
                    let msg = e.to_string();
                    if msg.contains(&format!("status:{}", status.as_str())) {
                        Ok(())
                    } else {
                        Err(Error::generic(eyre!("Error querying proposal `{proposal_id}`. Potential issues could be due to not using enough gas or the proposal submitted is invalid. Error: {e}")))
                    }
                }
            },
        )?;
        Ok(())
    }

    fn query_consumer_genesis(
        &self,
        consumer_chain_driver: &ChainDriver,
        consumer_chain_id: &str,
    ) -> Result<(), Error> {
        let consumer_genesis = query_consumer_genesis(
            self.chain_id.as_str(),
            &self.command_path,
            &self.home_path,
            &self.rpc_listen_address(),
            consumer_chain_id,
            &consumer_chain_driver.command_path,
        )?;
        consumer_chain_driver.write_file("config/consumer_genesis.json", &consumer_genesis)?;

        Ok(())
    }

    fn replace_genesis_state(&self) -> Result<(), Error> {
        let genesis_output = replace_genesis_state(self.chain_id.as_str(), &self.home_path)?;
        self.write_file("config/genesis.json", &genesis_output)?;

        Ok(())
    }

    fn copy_validator_key_pair(&self, provider_chain_driver: &ChainDriver) -> Result<(), Error> {
        copy_validator_key_pair(
            self.chain_id.as_str(),
            &provider_chain_driver.home_path,
            &self.home_path,
        )?;

        Ok(())
    }
}
