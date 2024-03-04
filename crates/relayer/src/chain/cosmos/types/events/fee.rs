use cometbft::abci::Event as AbciEvent;
use ibc_relayer_types::applications::ics29_fee::events::IncentivizedPacket;
use ibc_relayer_types::events::{IbcEvent, IbcEventType};

pub fn try_from_tx(event: &AbciEvent) -> Option<IbcEvent> {
    let event_type = event.kind.parse::<IbcEventType>().ok()?;

    if let IbcEventType::IncentivizedPacket = event_type {
        let event = IncentivizedPacket::try_from(&event.attributes[..]).ok()?;
        Some(IbcEvent::IncentivizedPacket(event))
    } else {
        None
    }
}
