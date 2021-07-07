//! Chain upgrade plans for triggering IBC-breaking upgrades.

use std::time::Duration;

use prost_types::Any;
use thiserror::Error;
use tracing::error;

use ibc::ics02_client::client_state::AnyClientState;
use ibc::ics02_client::height::Height;
use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc::{events::IbcEvent, ics07_tendermint::client_state::ClientState};
use ibc_proto::cosmos::gov::v1beta1::MsgSubmitProposal;
use ibc_proto::cosmos::upgrade::v1beta1::Plan;
use ibc_proto::ibc::core::client::v1::UpgradeProposal;

use crate::chain::{Chain, CosmosSdkChain};
use crate::config::ChainConfig;
use crate::error::Error;

#[derive(Debug, Error)]
pub enum UpgradeChainError {
    #[error("failed with underlying cause: {0}")]
    Failed(String),

    #[error("key error with underlying cause: {0}")]
    KeyError(Error),

    #[error(
        "failed during a transaction submission step to chain id {0} with underlying error: {1}"
    )]
    SubmitError(ChainId, Error),
}

#[derive(Clone, Debug)]
pub struct UpgradePlanOptions {
    pub src_chain_config: ChainConfig,
    pub dst_chain_config: ChainConfig,
    pub src_client_id: ClientId,
    pub amount: u64,
    pub height_offset: u64,
    pub upgraded_chain_id: ChainId,
    pub upgraded_unbonding_period: Option<Duration>,
    pub upgrade_plan_name: String,
}

pub fn build_and_send_ibc_upgrade_proposal(
    mut dst_chain: CosmosSdkChain, // the chain which will undergo an upgrade
    src_chain: CosmosSdkChain, // the source chain; supplies a client state for building the upgrade plan
    opts: &UpgradePlanOptions,
) -> Result<Vec<IbcEvent>, UpgradeChainError> {
    let upgrade_height = dst_chain
        .query_latest_height()
        .map_err(|e| UpgradeChainError::Failed(e.to_string()))?
        .add(opts.height_offset);

    let client_state = src_chain
        .query_client_state(&opts.src_client_id, Height::zero())
        .map_err(|e| UpgradeChainError::Failed(e.to_string()))?;

    // Retain the old unbonding period in case the user did not specify a new one
    let upgraded_unbonding_period = opts
        .upgraded_unbonding_period
        .unwrap_or(client_state.unbonding_period);

    let mut upgraded_client_state = ClientState::zero_custom_fields(client_state);
    upgraded_client_state.latest_height = upgrade_height.increment();
    upgraded_client_state.unbonding_period = upgraded_unbonding_period;
    upgraded_client_state.chain_id = opts.upgraded_chain_id.clone();

    let raw_client_state = AnyClientState::Tendermint(upgraded_client_state);
    let proposal = UpgradeProposal {
        title: "proposal 0".to_string(),
        description: "upgrade the chain software and unbonding period".to_string(),
        upgraded_client_state: Some(Any::from(raw_client_state)),
        plan: Some(Plan {
            name: opts.upgrade_plan_name.clone(),
            height: upgrade_height.revision_height as i64,
            info: "".to_string(),
        }),
    };

    let mut buf_proposal = Vec::new();
    prost::Message::encode(&proposal, &mut buf_proposal).unwrap();

    let any_proposal = Any {
        type_url: "/ibc.core.client.v1.UpgradeProposal".to_string(),
        value: buf_proposal,
    };

    // build the msg submit proposal
    let proposer = dst_chain
        .get_signer()
        .map_err(UpgradeChainError::KeyError)?;

    let coins = ibc_proto::cosmos::base::v1beta1::Coin {
        denom: "stake".to_string(),
        amount: opts.amount.to_string(),
    };

    let msg = MsgSubmitProposal {
        content: Some(any_proposal),
        initial_deposit: vec![coins],
        proposer: proposer.to_string(),
    };

    let mut buf_msg = Vec::new();
    prost::Message::encode(&msg, &mut buf_msg).unwrap();
    let any_msg = Any {
        type_url: "/cosmos.gov.v1beta1.MsgSubmitProposal".to_string(),
        value: buf_msg,
    };

    let events = dst_chain
        .send_msgs(vec![any_msg])
        .map_err(|e| UpgradeChainError::SubmitError(dst_chain.id().clone(), e))?;

    // Check if the chain rejected the transaction
    let result = events.iter().find_map(|event| match event {
        IbcEvent::ChainError(reason) => Some(reason.clone()),
        _ => None,
    });

    match result {
        None => Ok(events),
        Some(reason) => Err(UpgradeChainError::Failed(reason)),
    }
}
