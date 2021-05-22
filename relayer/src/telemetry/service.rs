
use std::sync::Arc;
use crossbeam_channel::Receiver;
use crate::telemetry::state::TelemetryState;

pub enum MetricUpdate {
    PacketsRelayed(u64)
}

pub struct TelemetryService {
    pub state: Arc<TelemetryState>,
    pub rx: Receiver<MetricUpdate>
}

impl TelemetryService {
    fn run(self) {
        while let Ok(update) = self.rx.recv() {
            self.apply_update(update);
        }
    }

    fn apply_update(&self, update: MetricUpdate) {
        match update {
            MetricUpdate::PacketsRelayed(n) => self.state.packets_relayed.add(n ),
        }
    }
}
