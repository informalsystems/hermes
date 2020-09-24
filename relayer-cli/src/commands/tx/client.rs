use crate::prelude::*;

use crate::application::app_config;
use crate::commands::utils::block_on;
use abscissa_core::{Command, Options, Runnable};
use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use ibc::ics02_client::client_type::ClientType;
use ibc::ics02_client::msgs::MsgCreateAnyClient;
use ibc::ics24_host::identifier::ClientId;
use ibc::ics24_host::Path::ClientState as ClientStatePath;
use ibc::tx_msg::Msg;
use prost_types::Any;
use relayer::chain::{query_latest_header, Chain, CosmosSDKChain};
use relayer::config::{ChainConfig, Config};
use relayer::error::{Error, Kind};
use std::time::Duration;
use tendermint::block::Height;

#[derive(Clone, Command, Debug, Options)]
pub struct TxCreateClientCmd {
    #[options(free, help = "identifier of the destination chain")]
    dest_chain_id: Option<String>,

    #[options(free, help = "identifier of the source chain")]
    src_chain_id: Option<String>,

    #[options(
        free,
        help = "identifier of the client for source chain to be created on destination chain"
    )]
    dest_client_id: Option<String>,
}

#[derive(Clone, Debug)]
pub struct CreateClientStateOptions {
    dest_client_id: ClientId,
    dest_chain_config: ChainConfig,
    src_chain_config: ChainConfig,
}

impl TxCreateClientCmd {
    fn validate_options(&self, config: &Config) -> Result<CreateClientStateOptions, String> {
        let dest_chain_id = self
            .dest_chain_id
            .clone()
            .ok_or_else(|| "missing destination chain identifier".to_string())?;

        let dest_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == dest_chain_id.parse().unwrap())
            .ok_or_else(|| "missing destination chain configuration".to_string())?;

        let src_chain_id = self
            .src_chain_id
            .clone()
            .ok_or_else(|| "missing source chain identifier".to_string())?;

        let src_chain_config = config
            .chains
            .iter()
            .find(|c| c.id == src_chain_id.parse().unwrap())
            .ok_or_else(|| "missing source chain configuration".to_string())?;

        let dest_client_id = self
            .dest_client_id
            .as_ref()
            .ok_or_else(|| "missing destination client identifier".to_string())?
            .parse()
            .map_err(|_| "bad client identifier".to_string())?;

        Ok(CreateClientStateOptions {
            dest_client_id,
            dest_chain_config: dest_chain_config.clone(),
            src_chain_config: src_chain_config.clone(),
        })
    }
}

impl Runnable for TxCreateClientCmd {
    fn run(&self) {
        let config = app_config();

        let opts = match self.validate_options(&config) {
            Err(err) => {
                status_err!("invalid options: {}", err);
                return;
            }
            Ok(result) => result,
        };
        status_info!("Message", "{:?}", opts);

        match create_client(opts) {
            Ok(receipt) => status_info!("client created, result: ", "{:?}", receipt),
            Err(e) => status_info!("client create failed, error: ", "{:?}", e),
        }
    }
}

pub fn create_client(opts: CreateClientStateOptions) -> Result<(), Error> {
    // Ger the destination
    let dest_chain = CosmosSDKChain::from_config(opts.clone().dest_chain_config)?;

    // Query the client state on destination chain.
    if dest_chain
        .abci_query(ClientStatePath(opts.clone().dest_client_id), 0, false)
        .is_ok()
    {
        return Err(Into::<Error>::into(Kind::CreateClient(
            opts.dest_client_id,
            "client already exists".into(),
        )));
    }

    // Get the latest header from the source chain and build the consensus state.
    let src_chain = CosmosSDKChain::from_config(opts.clone().src_chain_config)?;
    let tm_consensus_state = match block_on(query_latest_header::<CosmosSDKChain>(&src_chain)) {
        Err(err) => Err(Into::<Error>::into(
            Kind::CreateClient(
                opts.dest_client_id.clone(),
                "failed to get the latest header".into(),
            )
            .context(err),
        )),
        Ok(header) => {
            Ok(ibc::ics07_tendermint::consensus_state::ConsensusState::new_from_header(header))
        }
    }?;
    let any_consensus_state = AnyConsensusState::Tendermint(tm_consensus_state.clone());

    // Build the client state.
    let any_client_state = match ibc::ics07_tendermint::client_state::ClientState::new(
        src_chain.id().to_string(),
        src_chain.trusting_period(),
        src_chain.unbonding_period(),
        Duration::from_millis(3000),
        tm_consensus_state.height,
        Height(0),
    ) {
        Err(err) => Err(Into::<Error>::into(
            Kind::CreateClient(
                opts.dest_client_id.clone(),
                "failed to build the client state".into(),
            )
            .context(err),
        )),
        Ok(tm_state) => Ok(AnyClientState::Tendermint(tm_state)),
    }?;

    // Get the signer
    let signer = match dest_chain.config().account_prefix.parse() {
        Err(err) => Err(Into::<Error>::into(
            Kind::CreateClient(opts.dest_client_id.clone(), "bad signer".into()).context(err),
        )),
        Ok(signer) => Ok(signer),
    }?;

    // Build the domain type message
    let new_msg = MsgCreateAnyClient::new(
        opts.dest_client_id,
        ClientType::Tendermint,
        any_client_state,
        any_consensus_state,
        signer,
    );

    // Create a proto any message
    let mut proto_msgs: Vec<Any> = Vec::new();
    let any_msg = Any {
        // TODO - add get_url_type() to prepend proper string to get_type()
        type_url: "/ibc.client.MsgCreateClient".to_ascii_lowercase(),
        value: new_msg.get_sign_bytes(),
    };

    proto_msgs.push(any_msg);
    dest_chain.send(proto_msgs)
}
