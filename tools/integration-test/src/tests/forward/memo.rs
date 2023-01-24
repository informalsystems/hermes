//! These struct represent different scenarios for forward transfer.
//! The base structure is taken from https://github.com/strangelove-ventures/packet-forward-middleware#examples
//!
//!
//!

use serde::{Deserialize, Serialize};

pub trait HasForwardMemoInfo {
    fn new_memo(receiver: String, port: String, channel: String) -> Self;
}

#[derive(Serialize, Deserialize)]
pub struct MemoField<M: HasForwardMemoInfo> {
    forward: M,
}

impl<M: HasForwardMemoInfo> MemoField<M> {
    pub fn new(receiver: String, port: String, channel: String) -> Self {
        let forward = M::new_memo(receiver, port, channel);
        MemoField { forward }
    }
}

#[derive(Serialize, Deserialize)]
pub struct MemoMisspelledField<M: HasForwardMemoInfo> {
    fwd: M,
}

impl<M: HasForwardMemoInfo> MemoMisspelledField<M> {
    pub fn new(receiver: String, port: String, channel: String) -> Self {
        let fwd = M::new_memo(receiver, port, channel);
        MemoMisspelledField { fwd }
    }
}

#[derive(Serialize, Deserialize)]
pub struct MemoInfo {
    receiver: String,
    port: String,
    channel: String,
}

impl HasForwardMemoInfo for MemoInfo {
    fn new_memo(receiver: String, port: String, channel: String) -> Self {
        Self {
            receiver,
            port,
            channel,
        }
    }
}

#[derive(Serialize, Deserialize)]
pub struct MisspelledReceiverMemoInfo {
    recv: String,
    port: String,
    channel: String,
}

impl HasForwardMemoInfo for MisspelledReceiverMemoInfo {
    fn new_memo(receiver: String, port: String, channel: String) -> Self {
        Self {
            recv: receiver,
            port,
            channel,
        }
    }
}

#[derive(Serialize, Deserialize)]
pub struct MisspelledPortMemoInfo {
    receiver: String,
    fort: String,
    channel: String,
}

impl HasForwardMemoInfo for MisspelledPortMemoInfo {
    fn new_memo(receiver: String, port: String, channel: String) -> Self {
        Self {
            receiver,
            fort: port,
            channel,
        }
    }
}

#[derive(Serialize, Deserialize)]
pub struct MisspelledChannelMemoInfo {
    receiver: String,
    port: String,
    xhannel: String,
}

impl HasForwardMemoInfo for MisspelledChannelMemoInfo {
    fn new_memo(receiver: String, port: String, channel: String) -> Self {
        Self {
            receiver,
            port,
            xhannel: channel,
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
        intermediary_retries: u64,
        final_receiver: String,
        final_port: String,
        final_channel: String,
        final_timeout: String,
        final_retries: u64,
    ) -> Self {
        let hop_field = HopField::new(
            final_receiver,
            final_port,
            final_channel,
            final_timeout,
            final_retries,
        );
        let memo_content = HopMemoInfo::new(
            intermediary_receiver,
            intermediary_port,
            intermediary_channel,
            intermediary_timeout,
            intermediary_retries,
            hop_field,
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
    retries: u64,
    next: HopField,
}

impl HopMemoInfo {
    pub fn new(
        receiver: String,
        port: String,
        channel: String,
        timeout: String,
        retries: u64,
        next: HopField,
    ) -> Self {
        Self {
            receiver,
            port,
            channel,
            timeout,
            retries,
            next,
        }
    }
}

#[derive(Serialize, Deserialize)]
pub struct HopField {
    forward: Hop,
}

impl HopField {
    pub fn new(
        receiver: String,
        port: String,
        channel: String,
        timeout: String,
        retries: u64,
    ) -> Self {
        let hop = Hop::new(receiver, port, channel, timeout, retries);
        Self { forward: hop }
    }
}

#[derive(Serialize, Deserialize)]
pub struct Hop {
    receiver: String,
    port: String,
    channel: String,
    timeout: String,
    retries: u64,
}

impl Hop {
    pub fn new(
        receiver: String,
        port: String,
        channel: String,
        timeout: String,
        retries: u64,
    ) -> Self {
        Self {
            receiver,
            port,
            channel,
            timeout,
            retries,
        }
    }
}
