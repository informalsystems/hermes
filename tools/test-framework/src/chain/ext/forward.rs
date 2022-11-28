use ibc_relayer_types::core::ics24_host::identifier::{ChannelId, PortId};

use crate::prelude::{DualTagged, MonoTagged, WalletAddress};

/// Build the recipient address as following:
/// {intermediate_refund_address}|{foward_port}/{forward_channel}:{final_destination_address}
/// See <https://hub.cosmos.network/main/governance/proposals/2021-09-hub-ibc-router/>
pub fn build_forward_address<'a, ChainB, ChainC>(
    intermediate_destination_address: MonoTagged<ChainB, &'a WalletAddress>,
    port: DualTagged<ChainB, ChainC, PortId>,
    channel: &'a ChannelId,
    final_destination_address: MonoTagged<ChainC, &'a WalletAddress>,
) -> WalletAddress {
    let forward_address = format!(
        "{}|{}/{}:{}",
        intermediate_destination_address, port, channel, final_destination_address
    );
    WalletAddress(forward_address)
}

/// Build a forward address with the destination address invalid
pub fn build_invalid_forward_address<'a, ChainB, ChainC>(
    intermediate_destination_address: MonoTagged<ChainB, &'a WalletAddress>,
    port: DualTagged<ChainB, ChainC, PortId>,
    channel: &'a ChannelId,
) -> WalletAddress {
    let forward_address = format!(
        "{}|{}/{}:invalid address",
        intermediate_destination_address, port, channel
    );
    WalletAddress(forward_address)
}
