use color_eyre::eyre::Context;
use itertools::Itertools;

use tendermint::abci::{self, responses::Codespace, tag::Tag, Gas, Info, Log};

use crate::error::ReportError;

pub fn proto_to_deliver_tx(
    deliver_tx: tendermint_proto::abci::ResponseDeliverTx,
) -> Result<abci::DeliverTx, ReportError> {
    let events = deliver_tx
        .events
        .into_iter()
        .map(proto_to_abci_event)
        .try_collect()?;

    Ok(abci::DeliverTx {
        code: deliver_tx.code.into(),
        data: deliver_tx.data.into(),
        log: Log::new(deliver_tx.log),
        info: Info::new(deliver_tx.info),
        gas_wanted: Gas::from(deliver_tx.gas_wanted as u64),
        gas_used: Gas::from(deliver_tx.gas_used as u64),
        codespace: Codespace::new(deliver_tx.codespace),
        events,
    })
}

fn proto_to_abci_event(e: tendermint_proto::abci::Event) -> Result<abci::Event, ReportError> {
    let attributes = e
        .attributes
        .into_iter()
        .map(event_attribute_to_tag)
        .try_collect()?;

    Ok(abci::Event {
        type_str: e.r#type,
        attributes,
    })
}

fn event_attribute_to_tag(a: tendermint_proto::abci::EventAttribute) -> Result<Tag, ReportError> {
    let key = String::from_utf8(a.key).wrap_err("invalid utf-8 in event attribute key")?;
    let value = String::from_utf8(a.value).wrap_err("invalid utf-8 in event attribute value")?;

    Ok(Tag {
        key: key.into(),
        value: value.into(),
    })
}
