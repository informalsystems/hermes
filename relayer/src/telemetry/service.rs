use crossbeam_channel::Receiver;
use crate::telemetry::state::TelemetryState;

pub enum MetricUpdate {
    RelayChainsNumber(u64)
}

pub struct TelemetryService {
    pub state: TelemetryState,
    pub rx: Receiver<MetricUpdate>
}

impl TelemetryService {
    pub(crate) fn new(state: TelemetryState, rx: Receiver<MetricUpdate>) -> Self {
        Self {
            state,
            rx,
        }
    }

    pub(crate) fn run(self) {
        while let Ok(update) = self.rx.recv() {
            self.apply_update(update);
        }
    }

    fn apply_update(&self, update: MetricUpdate) {
        match update {
            MetricUpdate::RelayChainsNumber(n) => self.state.relay_chains_num.add(n ),
        }
    }
}
