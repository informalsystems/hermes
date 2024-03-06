use crate::chain::config::set_voting_period;
use crate::prelude::*;

use ibc_relayer::chain::tracking::TrackedMsgs;
use ibc_relayer::config::ChainConfig;
use ibc_relayer::event::IbcEventWithHeight;
use ibc_relayer_types::applications::ics27_ica::msgs::send_tx::MsgSendTx;
use ibc_relayer_types::applications::ics27_ica::packet_data::InterchainAccountPacketData;
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::timestamp::Timestamp;
use ibc_relayer_types::tx_msg::Msg;

pub fn update_genesis_for_consumer_chain(genesis: &mut serde_json::Value) -> Result<(), Error> {
    // Consumer chain doesn't have a gov key.
    if genesis
        .get_mut("app_state")
        .and_then(|app_state| app_state.get("gov"))
        .is_some()
    {
        set_voting_period(genesis, 10)?;
    }
    Ok(())
}

pub fn update_relayer_config_for_consumer_chain(config: &mut Config) {
    // The `ccv_consumer_chain` must be `true` for the Consumer chain.
    // The `trusting_period` must be strictly smaller than the `unbonding_period`
    // specified in the Consumer chain proposal. The test framework uses 100s in
    // the proposal.
    for chain_config in config.chains.iter_mut() {
        match chain_config {
            ChainConfig::CosmosSdk(chain_config)
                if chain_config.id == ChainId::from_string("ibcconsumer") =>
            {
                chain_config.ccv_consumer_chain = true;
                chain_config.trusting_period = Some(Duration::from_secs(99));
            }
            ChainConfig::CosmosSdk(_) => {}
        }
    }
}

/// Sends a message containing `InterchainAccountPacketData` from the `Signer`
/// to the `Chain`.
pub fn interchain_send_tx<ChainA: ChainHandle>(
    chain: &ChainA,
    from: &Signer,
    connection: &ConnectionId,
    msg: InterchainAccountPacketData,
    relative_timeout: Timestamp,
) -> Result<Vec<IbcEventWithHeight>, Error> {
    let msg = MsgSendTx {
        owner: from.clone(),
        connection_id: connection.clone(),
        packet_data: msg,
        relative_timeout,
    };

    let msg_any = msg.to_any();

    let tm = TrackedMsgs::new_static(vec![msg_any], "SendTx");

    chain
        .send_messages_and_wait_commit(tm)
        .map_err(Error::relayer)
}
