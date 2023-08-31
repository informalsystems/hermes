use alloc::sync::Arc;
use ibc_relayer_components::transaction::traits::event::CanParseTxResponseAsEvents;
use tendermint::abci::Event as AbciEvent;
use tendermint_rpc::endpoint::tx::Response as TxResponse;

use crate::contexts::transaction::CosmosTxContext;
use crate::types::error::Error;

impl CanParseTxResponseAsEvents for CosmosTxContext {
    fn parse_tx_response_as_events(
        response: TxResponse,
    ) -> Result<Vec<Vec<Arc<AbciEvent>>>, Error> {
        let events = split_events_by_messages(response.tx_result.events);

        Ok(events)
    }
}

fn split_events_by_messages(in_events: Vec<AbciEvent>) -> Vec<Vec<Arc<AbciEvent>>> {
    let mut out_events = Vec::new();
    let mut current_events = Vec::new();
    let mut first_message_event_found = false;

    for event in in_events.into_iter() {
        // TODO: What is the purpose of this filter ?
        // It seems that the event kind "message" from the Tx Response of some chains
        // only have 1 event attribute:
        // event kind: message
        // event attributes: [
        // EventAttribute {
        //    key: "sender",
        //   value: "cosmos1w2jl4lt77j0u3wuvknmrflp9pmwx5zmrr2j8x7",
        //  index: true,
        // },
        // ]
        // But others have multiple event attributes:
        // event kind in send_message: message
        // event.attributes: [
        // EventAttribute {
        // key: "action",
        //  value: "/ibc.core.channel.v1.MsgAcknowledgement",
        //   index: true,
        // },
        // EventAttribute {
        //   key: "sender",
        //   value: "cosmos1zl89j8asalm9s7gd5spskxtmh4l49lzs86auqx",
        //   index: true,
        // },
        // ]
        //
        //if event.kind == "message"
        //    && event.attributes.len() == 1
        //    && &event.attributes[0].key == "action"

        if event.kind == "message" && event.attributes.iter().any(|attr| attr.key == "action") {
            if first_message_event_found {
                out_events.push(current_events);
            } else {
                first_message_event_found = true;
            }

            current_events = vec![Arc::new(event)];
        } else if first_message_event_found {
            current_events.push(Arc::new(event));
        }
    }

    if !current_events.is_empty() {
        out_events.push(current_events);
    }

    out_events
}
