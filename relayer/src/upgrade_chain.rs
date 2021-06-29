use std::time::Duration;

use flex_error::define_error;
use ibc::ics02_client::client_state::AnyClientState;
use ibc::ics02_client::height::Height;
use ibc::ics24_host::identifier::{ChainId, ClientId};
use ibc::{events::IbcEvent, ics07_tendermint::client_state::ClientState};
use ibc_proto::cosmos::gov::v1beta1::MsgSubmitProposal;
use ibc_proto::cosmos::upgrade::v1beta1::{Plan, SoftwareUpgradeProposal};
use prost_types::Any;

use crate::chain::{Chain, CosmosSdkChain};
use crate::config::ChainConfig;
use crate::error::Error;

define_error! {
    UpgradeChainError {
        Key
            [ Error ]
            |_| { "key error" },

        Submit
            { chain_id: ChainId }
            [ Error ]
            |e| {
                format!("failed while submitting the Transfer message to chain {0}",
                    e.chain_id)
            },

        TxResponse
            { event: String }
            |e| {
                format!("tx response event consists of an error: {}",
                    e.event)
            },

    }
}

#[derive(Clone, Debug)]
pub struct UpdatePlanOptions {
    pub src_chain_config: ChainConfig,
    pub dst_chain_config: ChainConfig,
    pub src_client_id: ClientId,
    pub amount: u64,
    pub height_offset: u64,
}

pub fn build_and_send_upgrade_chain_message(
    mut dst_chain: CosmosSdkChain, // the chain whose account is debited
    src_chain: CosmosSdkChain,     // the chain where the transfer is sent
    opts: &UpdatePlanOptions,
) -> Result<Vec<IbcEvent>, UpgradeChainError> {
    // build a proposal Plan
    let upgrade_height = dst_chain
        .query_latest_height()
        .unwrap()
        .add(opts.height_offset);

    let client_state = src_chain
        .query_client_state(&opts.src_client_id, Height::zero())
        .unwrap();

    let mut upgraded_client_state = ClientState::zero_custom_fields(client_state);
    upgraded_client_state.latest_height = upgrade_height.increment();
    upgraded_client_state.unbonding_period = Duration::from_secs(400 * 3600);

    let raw_client_state = AnyClientState::Tendermint(upgraded_client_state);
    let plan = Plan {
        name: "test".to_string(),
        time: None,
        height: upgrade_height.revision_height as i64,
        info: "upgrade the chain software and unbonding period".to_string(),
        upgraded_client_state: Some(Any::from(raw_client_state)),
    };

    // build the proposal
    let proposal = SoftwareUpgradeProposal {
        title: "upgrade_ibc_clients".to_string(),
        description: "upgrade the chain software and unbonding period".to_string(),
        plan: Some(plan),
    };

    let mut buf_proposal = Vec::new();
    prost::Message::encode(&proposal, &mut buf_proposal).unwrap();

    let any_proposal = Any {
        type_url: "/cosmos.upgrade.v1beta1.SoftwareUpgradeProposal".to_string(),
        value: buf_proposal,
    };

    // build the msg submit proposal
    let proposer = dst_chain.get_signer().map_err(key_error)?;

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
        .map_err(|e| submit_error(dst_chain.id().clone(), e))?;

    // Check if the chain rejected the transaction
    let result = events.iter().find_map(|event| match event {
        IbcEvent::ChainError(reason) => Some(reason.clone()),
        _ => None,
    });

    match result {
        None => Ok(events),
        Some(reason) => Err(tx_response_error(reason)),
    }
}
