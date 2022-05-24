//! These are definitions of messages that a relayer submits to a chain. Specific implementations of
//! these messages can be found, for instance, in ICS 07 for Tendermint-specific chains. A chain
//! handles these messages in two layers: first with the general ICS 02 client handler, which
//! subsequently calls into the chain-specific (e.g., ICS 07) client handler. See:
//! <https://github.com/cosmos/ibc/tree/master/spec/core/ics-002-client-semantics#create>.

use crate::core::ics02_client::msgs::create_client::MsgCreateAnyClient;
use crate::core::ics02_client::msgs::misbehavior::MsgSubmitAnyMisbehaviour;
use crate::core::ics02_client::msgs::update_client::MsgUpdateAnyClient;
use crate::core::ics02_client::msgs::upgrade_client::MsgUpgradeAnyClient;

pub mod create_client;
pub mod misbehavior;
pub mod update_client;
pub mod upgrade_client;

#[allow(clippy::large_enum_variant)]
#[derive(Clone, Debug)]
pub enum ClientMsg {
    CreateClient(MsgCreateAnyClient),
    UpdateClient(MsgUpdateAnyClient),
    Misbehaviour(MsgSubmitAnyMisbehaviour),
    UpgradeClient(MsgUpgradeAnyClient),
}
