//! Utility functions for integration tests.

use ibc_relayer::chain::tracking::TrackedMsgs;
use ibc_relayer::event::IbcEventWithHeight;
use ibc_relayer_types::applications::ics27_ica::msgs::send_tx::MsgSendTx;
use ibc_relayer_types::applications::ics27_ica::packet_data::InterchainAccountPacketData;
use ibc_relayer_types::signer::Signer;
use ibc_relayer_types::timestamp::Timestamp;
use ibc_relayer_types::tx_msg::Msg;
use ibc_test_framework::prelude::*;

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
