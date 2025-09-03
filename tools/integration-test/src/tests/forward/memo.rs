//! These struct represent different scenarios for forward transfer.
//! The base structure of the memos are taken from
//! https://github.com/strangelove-ventures/packet-forward-middleware#examples

use serde::{Deserialize, Serialize};

pub trait HasForwardMemoInfo {
    fn new_memo(receiver: String, port: String, channel: String, timeout: u64) -> Self;
}

#[derive(Serialize, Deserialize)]
pub struct MemoField<M: HasForwardMemoInfo> {
    forward: M,
}

impl<M: HasForwardMemoInfo> MemoField<M> {
    pub fn new(receiver: String, port: String, channel: String, timeout: u64) -> Self {
        let forward = M::new_memo(receiver, port, channel, timeout);
        MemoField { forward }
    }
}

#[derive(Serialize, Deserialize)]
pub struct MemoMisspelledField<M: HasForwardMemoInfo> {
    fwd: M,
}

impl<M: HasForwardMemoInfo> MemoMisspelledField<M> {
    pub fn new(receiver: String, port: String, channel: String, timeout: u64) -> Self {
        let fwd = M::new_memo(receiver, port, channel, timeout);
        MemoMisspelledField { fwd }
    }
}

#[derive(Serialize, Deserialize)]
pub struct MemoInfo {
    receiver: String,
    port: String,
    channel: String,
    timeout: u64,
}

impl HasForwardMemoInfo for MemoInfo {
    fn new_memo(receiver: String, port: String, channel: String, timeout: u64) -> Self {
        Self {
            receiver,
            port,
            channel,
            timeout,
        }
    }
}

#[derive(Serialize, Deserialize)]
pub struct MisspelledReceiverMemoInfo {
    recv: String,
    port: String,
    channel: String,
    timeout: u64,
}

impl HasForwardMemoInfo for MisspelledReceiverMemoInfo {
    fn new_memo(receiver: String, port: String, channel: String, timeout: u64) -> Self {
        Self {
            recv: receiver,
            port,
            channel,
            timeout,
        }
    }
}

#[derive(Serialize, Deserialize)]
pub struct MisspelledPortMemoInfo {
    receiver: String,
    fort: String,
    channel: String,
    timeout: u64,
}

impl HasForwardMemoInfo for MisspelledPortMemoInfo {
    fn new_memo(receiver: String, port: String, channel: String, timeout: u64) -> Self {
        Self {
            receiver,
            fort: port,
            channel,
            timeout,
        }
    }
}

#[derive(Serialize, Deserialize)]
pub struct MisspelledChannelMemoInfo {
    receiver: String,
    port: String,
    xhannel: String,
    timeout: u64,
}

impl HasForwardMemoInfo for MisspelledChannelMemoInfo {
    fn new_memo(receiver: String, port: String, channel: String, timeout: u64) -> Self {
        Self {
            receiver,
            port,
            xhannel: channel,
            timeout,
        }
    }
}

#[derive(Serialize, Deserialize)]
pub struct HopMemoField {
    forward: HopMemoInfo,
}

impl HopMemoField {
    pub fn new(
        intermediary_receiver: String,
        intermediary_port: String,
        intermediary_channel: String,
        intermediary_timeout: String,
        final_receiver: String,
        final_port: String,
        final_channel: String,
        final_timeout: String,
    ) -> Self {
        let hop_field = HopField::new(final_receiver, final_port, final_channel, final_timeout);
        let hop_field_string = serde_json::to_string(&hop_field).unwrap();
        let memo_content = HopMemoInfo::new(
            intermediary_receiver,
            intermediary_port,
            intermediary_channel,
            intermediary_timeout,
            hop_field_string,
        );
        Self {
            forward: memo_content,
        }
    }
}

#[derive(Serialize, Deserialize)]
pub struct HopMemoInfo {
    receiver: String,
    port: String,
    channel: String,
    timeout: String,
    next: String,
}

impl HopMemoInfo {
    pub fn new(
        receiver: String,
        port: String,
        channel: String,
        timeout: String,
        next: String,
    ) -> Self {
        Self {
            receiver,
            port,
            channel,
            timeout,
            next,
        }
    }
}

#[derive(Serialize, Deserialize)]
pub struct HopField {
    forward: Hop,
}

impl HopField {
    pub fn new(receiver: String, port: String, channel: String, timeout: String) -> Self {
        let hop = Hop::new(receiver, port, channel, timeout);
        Self { forward: hop }
    }
}

#[derive(Serialize, Deserialize)]
pub struct Hop {
    receiver: String,
    port: String,
    channel: String,
    timeout: String,
}

impl Hop {
    pub fn new(receiver: String, port: String, channel: String, timeout: String) -> Self {
        Self {
            receiver,
            port,
            channel,
            timeout,
        }
    }
}
