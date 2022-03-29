//! Chain upgrade plans for triggering IBC-breaking upgrades.
#![allow(deprecated)] // TODO(hu55a1n1): remove this when we don't need legacy upgrade support

use core::time::Duration;

use bytes::BufMut;
use flex_error::define_error;

use tendermint::abci::transaction::Hash as TxHash;

use ibc::clients::ics07_tendermint::client_state::UpgradeOptions;
use ibc::core::ics02_client::client_state::{AnyClientState, ClientState};
use ibc::core::ics02_client::height::Height;
use ibc::core::ics24_host::identifier::{ChainId, ClientId};
use ibc::downcast;
use ibc_proto::cosmos::gov::v1beta1::MsgSubmitProposal;
use ibc_proto::cosmos::upgrade::v1beta1::{Plan, SoftwareUpgradeProposal};
use ibc_proto::google::protobuf::Any;
use ibc_proto::ibc::core::client::v1::UpgradeProposal;

use crate::chain::tx::TrackedMsgs;
use crate::chain::{ChainEndpoint, CosmosSdkChain};
use crate::config::ChainConfig;
use crate::error::Error;

define_error! {
    UpgradeChainError {
        Query
            [ Error ]
            |_| { "error during a query" },

        Key
            [ Error ]
            |_| { "key error" },

        Submit
            { chain_id: ChainId }
            [ Error ]
            |e| {
                format!("failed while submitting the Transfer message to chain {0}", e.chain_id)
            },

        TxResponse
            { event: String }
            |e| {
                format!("tx response event consists of an error: {}", e.event)
            },

        TendermintOnly
            |_| { "only Tendermint clients can be upgraded" }
    }
}

#[derive(Clone, Debug)]
pub struct UpgradePlanOptions {
    pub src_chain_config: ChainConfig,
    pub dst_chain_config: ChainConfig,
    pub src_client_id: ClientId,
    pub amount: u64,
    pub denom: String,
    pub height_offset: u64,
    pub upgraded_chain_id: ChainId,
    pub upgraded_unbonding_period: Option<Duration>,
    pub upgrade_plan_name: String,
    pub legacy: bool,
}

pub fn build_and_send_ibc_upgrade_proposal(
    mut dst_chain: CosmosSdkChain, // the chain which will undergo an upgrade
    src_chain: CosmosSdkChain, // the source chain; supplies a client state for building the upgrade plan
    opts: &UpgradePlanOptions,
) -> Result<TxHash, UpgradeChainError> {
    let upgrade_height = dst_chain
        .query_latest_height()
        .map_err(UpgradeChainError::query)?
        .add(opts.height_offset);

    let client_state = src_chain
        .query_client_state(&opts.src_client_id, Height::zero())
        .map_err(UpgradeChainError::query)?;

    let client_state = downcast!(client_state => AnyClientState::Tendermint)
        .ok_or_else(UpgradeChainError::tendermint_only)?;

    // Retain the old unbonding period in case the user did not specify a new one
    let upgrade_options = UpgradeOptions {
        unbonding_period: opts
            .upgraded_unbonding_period
            .unwrap_or(client_state.unbonding_period),
    };

    let upgraded_client_state = client_state.upgrade(
        upgrade_height.increment(),
        upgrade_options,
        opts.upgraded_chain_id.clone(),
    );

    let proposal = UpgradeProposal {
        title: "proposal 0".to_string(),
        description: "upgrade the chain software and unbonding period".to_string(),
        upgraded_client_state: Some(Any::from(upgraded_client_state.wrap_any())),
        plan: Some(Plan {
            name: opts.upgrade_plan_name.clone(),
            height: upgrade_height.revision_height as i64,
            info: "".to_string(),
            ..Default::default() // deprecated fields - time & upgraded_client_state
        }),
    };

    let proposal = if opts.legacy {
        Proposal::Legacy(proposal.into())
    } else {
        Proposal::Default(proposal)
    };

    let mut buf_proposal = Vec::new();
    proposal.encode(&mut buf_proposal);
    let any_proposal = Any {
        type_url: proposal.type_url(),
        value: buf_proposal,
    };

    // build the msg submit proposal
    let proposer = dst_chain.get_signer().map_err(UpgradeChainError::key)?;

    let coins = ibc_proto::cosmos::base::v1beta1::Coin {
        denom: opts.denom.clone(),
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

    // Can't use send_messages_and_wait_commit because no IBC events
    // corresponding to the transaction can be recognized to confirm the
    // upgrade.
    // https://github.com/informalsystems/ibc-rs/issues/1288#issuecomment-1066884163

    let responses = dst_chain
        .send_messages_and_wait_check_tx(TrackedMsgs::new_single(any_msg, "upgrade"))
        .map_err(|e| UpgradeChainError::submit(dst_chain.id().clone(), e))?;

    Ok(responses[0].hash)
}

enum Proposal {
    Default(UpgradeProposal),
    Legacy(LegacyProposal),
}

impl Proposal {
    fn encode(&self, buf: &mut impl BufMut) {
        match self {
            Proposal::Default(p) => prost::Message::encode(p, buf),
            Proposal::Legacy(p) => prost::Message::encode(&p.0, buf),
        }
        .unwrap()
    }

    fn type_url(&self) -> String {
        match self {
            Proposal::Default(_) => "/ibc.core.client.v1.UpgradeProposal",
            Proposal::Legacy(_) => "/cosmos.upgrade.v1beta1.SoftwareUpgradeProposal",
        }
        .to_owned()
    }
}

struct LegacyProposal(SoftwareUpgradeProposal);

impl From<UpgradeProposal> for LegacyProposal {
    fn from(v: UpgradeProposal) -> Self {
        let plan = {
            if let Some(plan) = v.plan {
                Some(Plan {
                    name: plan.name,
                    height: plan.height,
                    info: plan.info,
                    time: None,
                    upgraded_client_state: v.upgraded_client_state,
                })
            } else {
                None
            }
        };
        Self(SoftwareUpgradeProposal {
            title: v.title,
            description: v.description,
            plan,
        })
    }
}
