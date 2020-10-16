use prost_types::Any;
use std::convert::TryInto;
use std::time::Duration;

use ibc::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use ibc::ics02_client::client_type::ClientType;
use ibc::ics02_client::msgs::MsgCreateAnyClient;
use ibc::ics24_host::identifier::ClientId;
use ibc::ics24_host::Path::ClientState as ClientStatePath;
use ibc::tx_msg::Msg;

use tendermint::block::Height;

use crate::chain::cosmos::block_on;
use crate::chain::{query_latest_header, Chain, CosmosSDKChain};
use crate::config::ChainConfig;
use crate::error::{Error, Kind};

#[derive(Clone, Debug)]
pub struct CreateClientOptions {
    pub dest_client_id: ClientId,
    pub dest_chain_config: ChainConfig,
    pub src_chain_config: ChainConfig,
}

pub fn create_client(opts: CreateClientOptions) -> Result<Vec<u8>, Error> {
    // Get the destination chain
    let mut dest_chain = CosmosSDKChain::from_config(opts.clone().dest_chain_config)?;

    // Query the client state on destination chain.
    let response = dest_chain.query(
        ClientStatePath(opts.clone().dest_client_id),
        0_u64.try_into().unwrap(),
        false,
    );

    if response.is_ok() {
        return Err(Into::<Error>::into(Kind::CreateClient(
            opts.dest_client_id,
            "client already exists".into(),
        )));
    }

    // Get the latest header from the source chain and build the consensus state.
    let src_chain = CosmosSDKChain::from_config(opts.clone().src_chain_config)?;
    let tm_latest_header =
        block_on(query_latest_header::<CosmosSDKChain>(&src_chain)).map_err(|e| {
            Kind::CreateClient(
                opts.dest_client_id.clone(),
                "failed to get the latest header".into(),
            )
            .context(e)
        })?;

    let height = tm_latest_header.signed_header.header.height;

    let tm_consensus_state = ibc::ics07_tendermint::consensus_state::ConsensusState::from(
        tm_latest_header.signed_header,
    );

    let any_consensus_state = AnyConsensusState::Tendermint(tm_consensus_state);

    // Build the client state.
    let any_client_state = ibc::ics07_tendermint::client_state::ClientState::new(
        src_chain.id().to_string(),
        src_chain.trusting_period(),
        src_chain.unbonding_period(),
        Duration::from_millis(3000),
        height,
        0_u64.try_into().unwrap(),
        false,
        false,
    )
    .map_err(|e| {
        Kind::CreateClient(
            opts.dest_client_id.clone(),
            "failed to build the client state".into(),
        )
        .context(e)
    })
    .map(AnyClientState::Tendermint)?;

    let signer = dest_chain.config().account_prefix.parse().map_err(|e| {
        Kind::CreateClient(opts.dest_client_id.clone(), "bad signer".into()).context(e)
    })?;

    // Build the domain type message
    let new_msg = MsgCreateAnyClient::new(
        opts.dest_client_id,
        ClientType::Tendermint,
        any_client_state,
        any_consensus_state,
        signer,
    );

    let msg_type = "/ibc.client.MsgCreateClient".to_ascii_lowercase();

    let response = dest_chain.send(msg_type, new_msg.get_sign_bytes(), "".to_string(), 0)
        .map_err(|e| Kind::MessageTransaction("failed to create client".to_string()).context(e))?;

    Ok(response)
}
