use ibc::core::ics04_channel::events::WriteAcknowledgement;
use ibc::events::IbcEventType;
use ibc::signer::Signer;
use ibc_relayer::chain::cosmos::types::config::TxConfig;
use ibc_relayer::event::extract_packet_and_write_ack_from_tx;
use ibc_relayer::keyring::KeyEntry;
use ibc_relayer_framework::one_for_all::traits::runtime::OfaRuntimeContext;
use tendermint::abci::Event as AbciEvent;

use crate::cosmos::context::runtime::CosmosRuntime;
use crate::cosmos::error::Error;

#[derive(Clone)]
pub struct CosmosChainContext<Handle> {
    pub handle: Handle,
    pub signer: Signer,
    pub tx_config: TxConfig,
    pub key_entry: KeyEntry,
    pub runtime: OfaRuntimeContext<CosmosRuntime>,
}

impl<Handle> CosmosChainContext<Handle> {
    pub fn new(handle: Handle, signer: Signer, tx_config: TxConfig, key_entry: KeyEntry) -> Self {
        let runtime = OfaRuntimeContext::new(CosmosRuntime);

        Self {
            handle,
            signer,
            tx_config,
            key_entry,
            runtime,
        }
    }
}

pub struct WriteAcknowledgementEvent(pub WriteAcknowledgement);

impl TryFrom<AbciEvent> for WriteAcknowledgementEvent {
    type Error = Error;

    fn try_from(event: AbciEvent) -> Result<Self, Error> {
        if let Ok(IbcEventType::WriteAck) = event.type_str.parse() {
            let (packet, write_ack) =
                extract_packet_and_write_ack_from_tx(&event).map_err(Error::channel)?;

            let ack = WriteAcknowledgement {
                packet,
                ack: write_ack,
            };

            Ok(WriteAcknowledgementEvent(ack))
        } else {
            Err(Error::mismatch_event_type(
                "write_acknowledgement".to_string(),
                event.type_str.to_string(),
            ))
        }
    }
}
