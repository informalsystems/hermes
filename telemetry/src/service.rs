use std::sync::Arc;

use crossbeam_channel::Receiver;

use crate::state::TelemetryState;

#[derive(Debug)]
pub enum MetricUpdate {
    RelayChainsNumber(u64),
    RelayChannelsNumber(u64),
    TxCount(u64),
    TxSuccess(u64),
    TxFailed(u64),
    IbcAcknowledgePacket(u64),
    IbcRecvPacket(u64),
    IbcTransferSend(u64),
    IbcTransferReceive(u64),
    TimeoutPacket(u64),
}

pub fn run(telemetry_state: Arc<TelemetryState>, rx: Receiver<MetricUpdate>) {
    let service = TelemetryService::new(telemetry_state, rx);
    service.run()
}

#[derive(Debug)]
pub struct TelemetryService {
    state: Arc<TelemetryState>,
    rx: Receiver<MetricUpdate>,
}

impl TelemetryService {
    pub fn new(state: Arc<TelemetryState>, rx: Receiver<MetricUpdate>) -> Self {
        Self { state, rx }
    }

    pub fn run(self) {
        while let Ok(update) = self.rx.recv() {
            self.apply_update(update);
        }
    }

    fn apply_update(&self, update: MetricUpdate) {
        match update {
            MetricUpdate::RelayChainsNumber(n) => self.state.relay_chains_num.add(n),
            MetricUpdate::RelayChannelsNumber(n) => self.state.relay_channels_num.add(n),
            MetricUpdate::IbcAcknowledgePacket(n) => {
                self.state.tx_msg_ibc_acknowledge_packet.add(n)
            }
            MetricUpdate::IbcRecvPacket(n) => self.state.tx_msg_ibc_recv_packet.add(n),
            MetricUpdate::TxCount(n) => self.state.tx_count.add(n),
            MetricUpdate::TxSuccess(n) => self.state.tx_successful.add(n),
            MetricUpdate::TxFailed(n) => self.state.tx_failed.add(n),
            MetricUpdate::IbcTransferSend(n) => self.state.ibc_transfer_send.add(n),
            MetricUpdate::IbcTransferReceive(n) => self.state.ibc_transfer_receive.add(n),
            MetricUpdate::TimeoutPacket(n) => self.state.ibc_timeout_packet.add(n),
        }
    }
}
