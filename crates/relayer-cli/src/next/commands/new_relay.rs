use abscissa_core::clap::Parser;
use abscissa_core::{Command, Runnable};
use alloc::sync::Arc;
use tokio::runtime::Runtime as TokioRuntime;

use ibc_relayer_all_in_one::all_for_one::builder::CanBuildAfoBiRelay;
use ibc_relayer_components::relay::traits::components::auto_relayer::CanAutoRelay;
use ibc_relayer_cosmos::contexts::builder::CosmosBuilder;
use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId};

use crate::conclude::Output;
use crate::error::{handle_generic_error, Error};
use crate::prelude::*;

/// `relay` subcommands which utilize the experimental relayer architecture.
#[derive(Command, Debug, Parser, Runnable)]
pub enum NewRelayCmds {
    /// Relay all packets between two chains using the experimental
    /// relayer architecture.
    Packets(NewRelayPacketsCmd),
}

/// Encodes the CLI parameters of the experimental `relay packet` command
/// which utilizes the experimental relayer architecture.
#[derive(Debug, Parser, Command, PartialEq, Eq)]
pub struct NewRelayPacketsCmd {
    #[clap(
        long = "chain-a",
        required = true,
        value_name = "CHAIN_A_ID",
        help_heading = "REQUIRED",
        help = "Identifier of chain A"
    )]
    chain_a_id: ChainId,

    #[clap(
        long = "client-a",
        required = true,
        value_name = "CLIENT_A_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the client associated with chain A"
    )]
    client_a_id: ClientId,

    #[clap(
        long = "chain-b",
        required = true,
        value_name = "CHAIN_B_ID",
        help_heading = "REQUIRED",
        help = "Identifier of chain B"
    )]
    chain_b_id: ChainId,

    #[clap(
        long = "client-b",
        required = true,
        value_name = "CLIENT_B_ID",
        help_heading = "REQUIRED",
        help = "Identifier of the client associated with chain B"
    )]
    client_b_id: ClientId,
}

impl Runnable for NewRelayPacketsCmd {
    fn run(&self) {
        let config = app_config();

        let runtime = Arc::new(TokioRuntime::new().unwrap());

        let builder = CosmosBuilder::new_wrapped(
            (*config).clone(),
            runtime.clone(),
            Default::default(),
            Default::default(),
            Default::default(),
            Default::default(),
        );

        let res: Result<(), Error> = runtime.block_on(async {
            let birelay = builder
                .build_afo_birelay(
                    &self.chain_a_id,
                    &self.chain_b_id,
                    &self.client_a_id,
                    &self.client_b_id,
                )
                .await
                .map_err(handle_generic_error)?;

            birelay.auto_relay().await.map_err(handle_generic_error)?;

            Ok(())
        });

        if let Err(e) = res {
            Output::error(e).exit();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::NewRelayPacketsCmd;

    use std::str::FromStr;

    use abscissa_core::clap::Parser;
    use ibc_relayer_types::core::ics24_host::identifier::{ChainId, ClientId};

    #[test]
    fn test_new_relay_packets_required_only() {
        assert_eq!(
            NewRelayPacketsCmd {
                chain_a_id: ChainId::from_string("chain_a_id"),
                chain_b_id: ChainId::from_string("chain_b_id"),
                client_a_id: ClientId::from_str("client_a_id").unwrap(),
                client_b_id: ClientId::from_str("client_b_id").unwrap(),
            },
            NewRelayPacketsCmd::parse_from([
                "test",
                "--chain-a",
                "chain_a_id",
                "--client-a",
                "client_a_id",
                "--chain-b",
                "chain_b_id",
                "--client-b",
                "client_b_id",
            ])
        )
    }

    #[test]
    fn test_new_relay_packets_no_chain_id() {
        assert!(NewRelayPacketsCmd::try_parse_from([
            "test",
            "--client-a",
            "client_a_id",
            "--client-b",
            "client_b_id"
        ])
        .is_err())
    }

    #[test]
    fn test_new_relay_packets_no_client_id() {
        assert!(NewRelayPacketsCmd::try_parse_from([
            "test",
            "--chain-a",
            "chain_a_id",
            "--chain-b",
            "chain_b_id"
        ])
        .is_err())
    }
}
