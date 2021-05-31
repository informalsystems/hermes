use std::{thread, time::Duration};

use anomaly::BoxError;
use crossbeam_channel::Receiver;
use tracing::{debug, error, info, trace};

use ibc::{events::IbcEvent, ics02_client::events::UpdateClient};

use crate::{
    chain::handle::ChainHandlePair,
    foreign_client::{ForeignClient, ForeignClientError, MisbehaviourResults},
    object::Client,
};

use super::WorkerCmd;

pub struct ClientWorker {
    client: Client,
    chains: ChainHandlePair,
    cmd_rx: Receiver<WorkerCmd>,
}

impl ClientWorker {
    pub fn new(client: Client, chains: ChainHandlePair, cmd_rx: Receiver<WorkerCmd>) -> Self {
        Self {
            client,
            chains,
            cmd_rx,
        }
    }

    /// Run the event loop for events associated with a [`Client`].
    pub fn run(self) -> Result<(), BoxError> {
        let mut client = ForeignClient::restore(
            self.client.dst_client_id.clone(),
            self.chains.b.clone(),
            self.chains.a.clone(),
        );

        info!(
            "running client worker & initial misbehaviour detection for {}",
            client
        );

        // initial check for evidence of misbehaviour for all updates
        let skip_misbehaviour = self.detect_misbehaviour(&client, None);

        info!(
            "running client worker (misbehaviour and refresh) for {}",
            client
        );

        loop {
            thread::sleep(Duration::from_millis(600));

            // Run client refresh, exit only if expired or frozen
            if let Err(e @ ForeignClientError::ExpiredOrFrozen(..)) = client.refresh() {
                error!("failed to refresh client '{}': {}", client, e);
                return Err(Box::new(e));
            }

            if skip_misbehaviour {
                continue;
            }

            if let Ok(WorkerCmd::IbcEvents { batch }) = self.cmd_rx.try_recv() {
                trace!("client '{}' worker receives batch {:?}", client, batch);

                for event in batch.events {
                    if let IbcEvent::UpdateClient(update) = event {
                        debug!("client '{}' updated", client);

                        // Run misbehaviour. If evidence submitted the loop will exit in next
                        // iteration with frozen client
                        self.detect_misbehaviour(&client, Some(update));
                    }
                }
            }
        }
    }

    fn detect_misbehaviour(&self, client: &ForeignClient, update: Option<UpdateClient>) -> bool {
        match client.detect_misbehaviour_and_submit_evidence(update) {
            MisbehaviourResults::ValidClient => false,
            MisbehaviourResults::VerificationError => {
                // can retry in next call
                false
            }
            MisbehaviourResults::EvidenceSubmitted(_) => {
                // if evidence was submitted successfully then exit
                true
            }
            MisbehaviourResults::CannotExecute => {
                // skip misbehaviour checking if chain does not have support for it (i.e. client
                // update event does not include the header)
                true
            }
        }
    }

    /// Get a reference to the client worker's chains.
    pub fn chains(&self) -> &ChainHandlePair {
        &self.chains
    }

    /// Get a reference to the client worker's object.
    pub fn object(&self) -> &Client {
        &self.client
    }
}
