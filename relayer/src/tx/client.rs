use prost_types::Any;

use ibc_proto::ibc::core::client::v1::MsgCreateClient as RawMsgCreateClient;
use ibc_proto::ibc::core::client::v1::MsgUpdateClient as RawMsgUpdateClient;

use ibc::ics02_client::header::Header;
use ibc::ics02_client::msgs::create_client::MsgCreateAnyClient;
use ibc::ics02_client::msgs::update_client::MsgUpdateAnyClient;
use ibc::ics02_client::state::ClientState;
use ibc::ics02_client::state::ConsensusState;

use ibc::ics24_host::identifier::ClientId;

use ibc::tx_msg::Msg;
use ibc::Height;

use crate::chain::{handle::ChainHandle, runtime::ChainRuntime, Chain};
use crate::config::ChainConfig;
use crate::error::{Error, Kind};

#[derive(Clone, Debug)]
pub struct ClientOptions {
    pub dst_client_id: ClientId,
    pub dst_chain_config: ChainConfig,
    pub src_chain_config: ChainConfig,
    pub signer_seed: String,
}

pub fn build_create_client(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    dst_client_id: ClientId,
    signer_seed: String,
) -> Result<MsgCreateAnyClient, Error> {
    // Verify that the client has not been created already, i.e the destination chain does not
    // have a state for this client.
    let client_state = dst_chain.query_client_state(&dst_client_id, Height::default());
    if client_state.is_ok() {
        return Err(Into::<Error>::into(Kind::CreateClient(
            dst_client_id,
            "client already exists".into(),
        )));
    }

    // Get the signer from key seed file
    let (_, signer) = dst_chain.key_and_signer(signer_seed)?;

    // Build client create message with the data from source chain at latest height.
    let latest_height = src_chain.query_latest_height()?;
    Ok(MsgCreateAnyClient::new(
        dst_client_id,
        src_chain.build_client_state(latest_height)?.wrap_any(),
        src_chain.build_consensus_state(latest_height)?.wrap_any(),
        signer,
    )
    .map_err(|e| {
        Kind::MessageTransaction("failed to build the create client message".into()).context(e)
    })?)
}

pub fn build_create_client_and_send(opts: ClientOptions) -> Result<String, Error> {
    // Initialize the source and destination runtimes and light clients
    let (src_chain, _) = ChainRuntime::spawn(opts.src_chain_config.clone())?;
    let (dst_chain, _) = ChainRuntime::spawn(opts.dst_chain_config.clone())?;

    let new_msg = build_create_client(
        dst_chain.clone(),
        src_chain,
        opts.dst_client_id,
        opts.signer_seed.clone(),
    )?;

    let (key, _) = dst_chain.key_and_signer(opts.signer_seed)?;

    Ok(dst_chain.send_tx(
        vec![new_msg.to_any::<RawMsgCreateClient>()],
        key,
        "".to_string(),
        0,
    )?)
}

pub fn build_update_client(
    dst_chain: impl ChainHandle,
    src_chain: impl ChainHandle,
    dst_client_id: ClientId,
    target_height: Height,
    signer_seed: String,
) -> Result<Vec<Any>, Error> {
    // Get the latest trusted height from the client state on destination.
    let trusted_height = dst_chain
        .query_client_state(&dst_client_id, Height::default())?
        .latest_height();

    // Get the signer from key seed file.
    let (_, signer) = dst_chain.key_and_signer(signer_seed)?;

    let header = src_chain
        .build_header(trusted_height, target_height)?
        .wrap_any();

    let new_msg = MsgUpdateAnyClient {
        client_id: dst_client_id,
        header,
        signer,
    };

    Ok(vec![new_msg.to_any::<RawMsgUpdateClient>()])
}

pub fn build_update_client_and_send(opts: ClientOptions) -> Result<String, Error> {
    // Initialize the source and destination runtimes and light clients
    let (src_chain, _) = ChainRuntime::spawn(opts.src_chain_config.clone())?;
    let (dst_chain, _) = ChainRuntime::spawn(opts.dst_chain_config.clone())?;

    let target_height = src_chain.query_latest_height()?;
    let new_msgs = build_update_client(
        dst_chain.clone(),
        src_chain,
        opts.dst_client_id,
        target_height,
        opts.signer_seed.clone(),
    )?;

    let (key, _) = dst_chain.key_and_signer(opts.signer_seed)?;

    Ok(dst_chain.send_tx(new_msgs, key, "".to_string(), 0)?)
}
