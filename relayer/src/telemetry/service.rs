use crate::telemetry::state::TelemetryState;
use crossbeam_channel::Receiver;

pub enum MetricUpdate {
    RelayChainsNumber(u64),
    RelayChannelsNumber(u64),
    AcknowledgePacket(u64),
    TxCount(u64),
}

pub struct TelemetryService {
    pub state: TelemetryState,
    pub rx: Receiver<MetricUpdate>,
}

impl TelemetryService {
    pub(crate) fn new(state: TelemetryState, rx: Receiver<MetricUpdate>) -> Self {
        Self { state, rx }
    }

    pub(crate) fn run(self) {
        while let Ok(update) = self.rx.recv() {
            self.apply_update(update);
        }
    }

    fn apply_update(&self, update: MetricUpdate) {
        match update {
            MetricUpdate::RelayChainsNumber(n) => self.state.relay_chains_num.add(n),
            MetricUpdate::RelayChannelsNumber(n) => self.state.relay_channels_num.add(n),
            MetricUpdate::AcknowledgePacket(n) => self.state.tx_msg_ibc_acknowledge_packet.add(n),
            MetricUpdate::TxCount(n) => self.state.tx_count.add(n),
        }
    }
}
