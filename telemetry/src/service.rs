use std::sync::Arc;

use crossbeam_channel::Receiver;

use crate::{MetricUpdate, TelemetryState};

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
        use MetricUpdate::*;

        match update {
            TxCount(n) => self.state.tx_count.add(n),
            TxSuccess(n) => self.state.tx_successful.add(n),
            TxFailed(n) => self.state.tx_failed.add(n),
            RelayChainsNumber(n) => self.state.relay_chains_num.add(n),
            RelayChannelsNumber(n) => self.state.relay_channels_num.add(n),
            TimeoutPacket(n) => self.state.ibc_timeout_packet.add(n),
            IbcAcknowledgePacket(n) => self.state.tx_msg_ibc_acknowledge_packet.add(n),
            IbcRecvPacket(n) => self.state.tx_msg_ibc_recv_packet.add(n),
            IbcTransferSend(n) => self.state.ibc_transfer_send.add(n),
            IbcTransferReceive(n) => self.state.ibc_transfer_receive.add(n),
            IbcClientMisbehaviour(n) => self.state.ibc_client_misbehaviour.add(n),
        }
    }
}
