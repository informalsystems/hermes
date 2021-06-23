use tendermint::abci::tag::Tag as AbciTag;
use tendermint_rpc::event::{Event as RpcEvent, EventData as RpcEventData, EventData};

use ibc::events::{from_tx_response_event, IbcEvent};
use ibc::ics02_client::events::NewBlock;
use ibc::ics02_client::height::Height;
use ibc::ics24_host::identifier::ChainId;

pub fn get_all_events(
    chain_id: &ChainId,
    result: RpcEvent,
) -> Result<Vec<(Height, IbcEvent)>, String> {
    let mut vals: Vec<(Height, IbcEvent)> = vec![];

    match &result.data {
        RpcEventData::NewBlock { block, .. } => {
            let height = Height::new(
                ChainId::chain_version(chain_id.to_string().as_str()),
                u64::from(block.as_ref().ok_or("tx.height")?.header.height),
            );

            vals.push((height, NewBlock::new(height).into()));
        }
        EventData::Tx { tx_result } => {
            let height = Height::new(
                ChainId::chain_version(chain_id.to_string().as_str()),
                tx_result.height as u64,
            );
            for event in tx_result.result.events.iter() {
                let abci_event = tendermint::abci::Event {
                    type_str: event.event_type.to_string(),
                    attributes: event
                        .attributes
                        .iter()
                        .map(|rpc_tag| {
                            serde_json::from_str::<AbciTag>(
                                serde_json::to_string(rpc_tag).unwrap().as_str(),
                            )
                            .unwrap()
                        })
                        .collect(),
                };

                if let Some(ibc_event) = from_tx_response_event(height, &abci_event) {
                    tracing::trace!("Extracted ibc_event {:?}", ibc_event);
                    vals.push((height, ibc_event));
                }
            }
        }
        _ => {}
    }

    Ok(vals)
}
