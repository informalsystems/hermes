use crate::framework::binary::chain::run_self_connected_binary_chain_test;
use crate::framework::binary::channel::RunBinaryChannelTest;
use crate::ibc::denom::{derive_ibc_denom, Denom};
use crate::prelude::*;
use crate::types::tagged::mono::Tagged;

use super::itf::InformalTrace;
use super::state::{Action, State};

#[test]
fn test_ibc_transfer() -> Result<(), Error> {
    run_binary_channel_test(&IbcTransferMBT)
}

/**
   Test that IBC token transfer can still work with a single
   chain that is connected to itself.
*/
#[test]
fn test_self_connected_ibc_transfer() -> Result<(), Error> {
    run_self_connected_binary_chain_test(&RunBinaryChannelTest::new(&IbcTransferMBT))
}

pub struct IbcTransferMBT;

impl TestOverrides for IbcTransferMBT {}

fn get_chain<ChainA, ChainB, ChainC>(
    chains: &ConnectedChains<ChainA, ChainB>,
    chain_id: u64,
) -> Tagged<ChainC, &FullNode>
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
    ChainC: ChainHandle,
{
    Tagged::new(match chain_id {
        1 => chains.node_a.value(),
        2 => chains.node_b.value(),
        _ => unreachable!(),
    })
}

fn get_wallet<'a, ChainC>(
    wallets: &'a Tagged<ChainC, &TestWallets>,
    user: u64,
) -> Tagged<ChainC, &'a Wallet> {
    match user {
        1 => wallets.user1(),
        2 => wallets.user2(),
        _ => unreachable!(),
    }
}

fn get_denom<'a, ChainC>(
    chain: &'a Tagged<ChainC, &FullNode>,
    denom: u64,
) -> Tagged<ChainC, &'a Denom> {
    match denom {
        1 => chain.denom(),
        2 => chain.denom(),
        _ => unreachable!(),
    }
}

fn get_port_channel_id<ChainA, ChainB, ChainC, ChainD>(
    channel: &ConnectedChannel<ChainA, ChainB>,
    chain_id: u64,
) -> (
    DualTagged<ChainC, ChainD, &PortId>,
    DualTagged<ChainC, ChainD, &ChannelId>,
)
where
    ChainA: ChainHandle,
    ChainB: ChainHandle,
    ChainC: ChainHandle,
    ChainD: ChainHandle,
{
    let (port_id, channel_id) = match chain_id {
        1 => {
            let port_id = channel.port_a.value();
            let channel_id = channel.channel_id_a.value();
            (port_id, channel_id)
        }
        2 => {
            let port_id = channel.port_b.value();
            let channel_id = channel.channel_id_b.value();
            (port_id, channel_id)
        }
        _ => unreachable!(),
    };
    (DualTagged::new(port_id), DualTagged::new(channel_id))
}

impl BinaryChannelTest for IbcTransferMBT {
    fn run<ChainA: ChainHandle, ChainB: ChainHandle>(
        &self,
        _config: &TestConfig,
        chains: ConnectedChains<ChainA, ChainB>,
        channel: ConnectedChannel<ChainA, ChainB>,
    ) -> Result<(), Error> {
        let itf_path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/spec/example/counterexample.itf.json"
        );

        let itf_json = std::fs::read_to_string(itf_path).expect("itf file does not exist. did you run `apalache check --inv=Invariant --run-dir=run main.tla` first?");

        let t: InformalTrace<State> =
            serde_json::from_str(&itf_json).expect("deserialization error");

        for state in t.states {
            match state.action {
                Action::Null => {
                    info!("[Init] Initial State");
                }
                Action::LocalTransfer {
                    chain_id,
                    source,
                    target,
                    denom,
                    amount,
                } => {
                    let node: Tagged<ChainA, _> = get_chain(&chains, chain_id);
                    let wallets = node.wallets();

                    let source_wallet = get_wallet(&wallets, source);
                    let target_wallet = get_wallet(&wallets, target);
                    let denom = get_denom(&node, denom);

                    node.chain_driver().local_transfer_token(
                        &source_wallet.address(),
                        &target_wallet.address(),
                        amount,
                        &denom,
                    )?;
                }
                Action::CreateChannel { .. } => {
                    info!("[CreateChannel] Channel is created beforehand")
                }
                Action::ExpireChannel { .. } => {
                    info!("[ExpireChannel] Channel expiring is not supported")
                }
                Action::IBCTransferSendPacket { packet } => {
                    let node_source: Tagged<ChainA, _> =
                        get_chain(&chains, packet.channel.source.chain_id);
                    let node_target: Tagged<ChainB, _> =
                        get_chain(&chains, packet.channel.target.chain_id);

                    let wallets_source = node_source.wallets();
                    let wallets_target = node_target.wallets();

                    let wallet_source = get_wallet(&wallets_source, packet.from);
                    let wallet_target = get_wallet(&wallets_target, packet.to);
                    let denom_source = get_denom(&node_source, packet.denom);
                    let amount_source_to_target = packet.amount;

                    let (port_source, channel_id_source) =
                        get_port_channel_id(&channel, packet.channel.source.chain_id);

                    info!(
                        "[IBCTransferSendPacket] Sending IBC transfer from chain {} to chain {} with amount of {} {}",
                        node_source.chain_id(),
                        node_target.chain_id(),
                        amount_source_to_target,
                        denom_source,
                    );

                    node_source.chain_driver().transfer_token(
                        &port_source,
                        &channel_id_source,
                        &wallet_source.address(),
                        &wallet_target.address(),
                        amount_source_to_target,
                        &denom_source,
                    )?;
                }
                Action::IBCTransferReceivePacket { packet } => {
                    let node_source: Tagged<ChainA, _> =
                        get_chain(&chains, packet.channel.source.chain_id);
                    let node_target: Tagged<ChainB, _> =
                        get_chain(&chains, packet.channel.target.chain_id);

                    let wallets_target = node_target.wallets();

                    let wallet_target = get_wallet(&wallets_target, packet.to);
                    let denom_source = get_denom(&node_source, packet.denom);
                    let amount_source_to_target = packet.amount;

                    let (port_target, channel_id_target) =
                        get_port_channel_id(&channel, packet.channel.target.chain_id);

                    let denom_target =
                        derive_ibc_denom(&port_target, &channel_id_target, &denom_source)?;

                    info!(
                        "[IBCTransferReceivePacket] Waiting for user on chain {} to receive IBC transferred amount of {} {} (chain {}/{})",
                        node_target.chain_id(), amount_source_to_target, denom_target, node_source.chain_id(), denom_source
                    );

                    node_target.chain_driver().assert_eventual_wallet_amount(
                        &wallet_target,
                        amount_source_to_target,
                        &denom_target.as_ref(),
                    )?;
                }
                Action::IBCTransferAcknowledgePacket { packet } => {
                    let node_source: Tagged<ChainA, _> =
                        get_chain(&chains, packet.channel.source.chain_id);
                    let node_target: Tagged<ChainB, _> =
                        get_chain(&chains, packet.channel.target.chain_id);

                    let wallets_source = node_source.wallets();

                    let wallet_source = get_wallet(&wallets_source, packet.from);
                    let denom_source = get_denom(&node_source, packet.denom);
                    let amount_source_to_target = packet.amount;

                    let balance_source = node_source
                        .chain_driver()
                        .query_balance(&wallet_source.address(), &denom_source)?;

                    info!(
                        "[IBCTransferAcknowledgePacket] Waiting for user on chain {} to confirm IBC transferred amount of {} {}",
                        node_source.chain_id(), amount_source_to_target, denom_source
                    );

                    node_source.chain_driver().assert_eventual_wallet_amount(
                        &wallet_source,
                        balance_source - amount_source_to_target,
                        &denom_source,
                    )?;

                    info!(
                        "[IBCTransferAcknowledgePacket] Successfully performed IBC transfer from chain {} to chain {}",
                        node_source.chain_id(),
                        node_target.chain_id(),
                    );
                }
                Action::IBCTransferTimeoutPacket { .. } => {
                    info!("[IBCTransferTimeoutPacket] Packet timeout is not supported")
                }
            }
        }

        Ok(())
    }
}
