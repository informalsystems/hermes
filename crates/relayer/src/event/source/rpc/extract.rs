use tendermint::abci;

use ibc_relayer_types::applications::ics29_fee::events::DistributionType;
use ibc_relayer_types::core::ics02_client::height::Height;
use ibc_relayer_types::core::ics24_host::identifier::ChainId;
use ibc_relayer_types::events::IbcEvent;

use crate::telemetry;

use crate::event::{ibc_event_try_from_abci_event, IbcEventWithHeight};

pub fn extract_events(
    _chain_id: &ChainId,
    height: Height,
    events: &[abci::Event],
) -> Result<Vec<IbcEventWithHeight>, String> {
    let mut events_with_height = vec![];

    for abci_event in events {
        match ibc_event_try_from_abci_event(abci_event) {
            Ok(event) if should_collect_event(&event) => {
                if let IbcEvent::DistributeFeePacket(dist) = &event {
                    // Only record rewarded fees
                    if let DistributionType::Reward = dist.distribution_type {
                        telemetry!(fees_amount, _chain_id, &dist.receiver, dist.fee.clone());
                    }
                } else {
                    events_with_height.push(IbcEventWithHeight { height, event });
                }
            }

            _ => {}
        }
    }

    Ok(events_with_height)
}

fn should_collect_event(e: &IbcEvent) -> bool {
    event_is_type_packet(e)
        || event_is_type_channel(e)
        || event_is_type_connection(e)
        || event_is_type_client(e)
        || event_is_type_fee(e)
        || event_is_type_cross_chain_query(e)
}

fn event_is_type_packet(ev: &IbcEvent) -> bool {
    matches!(
        ev,
        IbcEvent::SendPacket(_)
            | IbcEvent::ReceivePacket(_)
            | IbcEvent::WriteAcknowledgement(_)
            | IbcEvent::AcknowledgePacket(_)
            | IbcEvent::TimeoutPacket(_)
            | IbcEvent::TimeoutOnClosePacket(_)
    )
}

fn event_is_type_client(ev: &IbcEvent) -> bool {
    matches!(
        ev,
        IbcEvent::CreateClient(_)
            | IbcEvent::UpdateClient(_)
            | IbcEvent::UpgradeClient(_)
            | IbcEvent::ClientMisbehaviour(_)
    )
}

fn event_is_type_connection(ev: &IbcEvent) -> bool {
    matches!(
        ev,
        IbcEvent::OpenInitConnection(_)
            | IbcEvent::OpenTryConnection(_)
            | IbcEvent::OpenAckConnection(_)
            | IbcEvent::OpenConfirmConnection(_)
    )
}

fn event_is_type_channel(ev: &IbcEvent) -> bool {
    matches!(
        ev,
        IbcEvent::OpenInitChannel(_)
            | IbcEvent::OpenTryChannel(_)
            | IbcEvent::OpenAckChannel(_)
            | IbcEvent::OpenConfirmChannel(_)
            | IbcEvent::CloseInitChannel(_)
            | IbcEvent::CloseConfirmChannel(_)
    )
}

fn event_is_type_cross_chain_query(ev: &IbcEvent) -> bool {
    matches!(ev, IbcEvent::CrossChainQueryPacket(_))
}

fn event_is_type_fee(ev: &IbcEvent) -> bool {
    matches!(
        ev,
        IbcEvent::IncentivizedPacket(_) | IbcEvent::DistributeFeePacket(_)
    )
}
