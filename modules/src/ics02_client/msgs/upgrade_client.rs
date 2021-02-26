//! Definition of domain type msg `MsgUpgradeAnyClient`.

use tendermint::account::Id as AccountId;

use crate::ics24_host::identifier::ClientId;
use crate::ics02_client::client_def::{AnyClientState, AnyConsensusState};
use crate::tx_msg::Msg;

pub(crate) const TYPE_URL: &str = "/ibc.core.client.v1.MsgUpgradeClient";

/// A type of message that triggers the upgrade of an on-chain (IBC) client.
#[derive(Clone, Debug, PartialEq)]
pub struct MsgUpgradeAnyClient {
    pub client_id: ClientId,
    pub client_state: AnyClientState,
    pub consensus_state: AnyConsensusState,
    pub proof_upgrade_client: String,
    pub proof_upgrade_consensus_state: String,
}


impl Msg for MsgUpgradeAnyClient {
    type ValidationError = crate::ics24_host::error::ValidationError;

    fn route(&self) -> String {
        crate::keys::ROUTER_KEY.to_string()
    }

    fn type_url(&self) -> String {
        TYPE_URL.to_string()
    }

    fn get_signers(&self) -> Vec<AccountId> {
        unimplemented!()
    }
}