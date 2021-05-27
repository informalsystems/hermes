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
            Worker(worker_type, op) => self.state.worker(worker_type, op),
            IbcClientMisbehaviour(chain, client) => {
                self.state.ibc_client_misbehaviour(&chain, &client)
            }
            ReceivePacket(chain, channel, port, count) => {
                self.state.receive_packets(&chain, &channel, &port, count)
            }
        }
    }
}
