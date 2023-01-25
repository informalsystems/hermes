//! These struct represent different scenarios for forward transfer.
//! The base structure of the memos are taken from
//! https://github.com/strangelove-ventures/packet-forward-middleware#examples

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
        final_receiver: String,
        final_port: String,
        final_channel: String,
    ) -> Self {
        let hop_field = HopField::new(final_receiver, final_port, final_channel);
        let hop_field_string = serde_json::to_string(&hop_field).unwrap();
        let memo_content = HopMemoInfo::new(
            intermediary_receiver,
            intermediary_port,
            intermediary_channel,
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
    next: String,
}

impl HopMemoInfo {
    pub fn new(receiver: String, port: String, channel: String, next: String) -> Self {
        Self {
            receiver,
            port,
            channel,
            next,
        }
    }
}

#[derive(Serialize, Deserialize)]
pub struct HopField {
    forward: Hop,
}

impl HopField {
    pub fn new(receiver: String, port: String, channel: String) -> Self {
        let hop = Hop::new(receiver, port, channel);
        Self { forward: hop }
    }
}

#[derive(Serialize, Deserialize)]
pub struct Hop {
    receiver: String,
    port: String,
    channel: String,
}

impl Hop {
    pub fn new(receiver: String, port: String, channel: String) -> Self {
        Self {
            receiver,
            port,
            channel,
        }
    }
}
