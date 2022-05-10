use color_eyre::eyre::Context;
use itertools::Itertools;
use sqlx::PgPool;
use tendermint_proto::abci::TxResult;
use tracing::info;

use tendermint::abci::{self, responses::Codespace, tag::Tag, Gas, Info, Log};
use tendermint_rpc::endpoint::tx::Response as TxResponse;
use tendermint_rpc::endpoint::tx_search::Response as TxSearchResponse;

use crate::error::ReportError;
use crate::search::TxSearch;

#[tracing::instrument(skip(pool))]
pub async fn tx_search(pool: &PgPool, search: TxSearch) -> Result<TxSearchResponse, ReportError> {
    info!(hash = ?search.hash, "got tx_hash");

    let raw_tx_result = tx_result_by_hash(pool, &search.hash).await?;
    let deliver_tx = raw_tx_result.result.unwrap();
    let tx_result = proto_to_deliver_tx(deliver_tx)?;

    dbg!(&tx_result.events);

    let txs = vec![TxResponse {
        hash: search.hash.parse().wrap_err("failed to parse tx hash")?, // TODO: validate hash earlier
        height: raw_tx_result.height.try_into().unwrap(),
        index: raw_tx_result.index,
        tx_result,
        tx: raw_tx_result.tx.into(),
        proof: None,
    }];

    Ok(TxSearchResponse {
        txs,
        total_count: 1,
    })
}

async fn tx_result_by_hash(pool: &PgPool, hash: &str) -> Result<TxResult, ReportError> {
    use prost::Message;

    let bytes = sqlx::query_scalar::<_, Vec<u8>>(
        "SELECT tx_result FROM tx_results WHERE tx_hash = $1 LIMIT 1",
    )
    .bind(hash)
    .fetch_one(pool)
    .await
    .wrap_err(format!("no tx found with hash '{hash}'"))?;

    let tx_result = tendermint_proto::abci::TxResult::decode(bytes.as_slice())
        .wrap_err("failed to decode tx result")?;

    Ok(tx_result)
}

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

// fn abci_events(event_attributes: Vec<EventAttribute>) -> Vec<abci::Event> {
//     use itertools::Itertools;

//     let map = event_attributes
//         .into_iter()
//         .into_group_map_by(|e| e.r#type.clone());

//     let mut events = Vec::new();

//     for (type_str, attrs) in map {
//         let event = abci::Event {
//             type_str,
//             attributes: attrs
//                 .into_iter()
//                 .map(|a| abci::tag::Tag {
//                     key: a.key.parse().unwrap(),     // Infallible
//                     value: a.value.parse().unwrap(), // Infallible
//                 })
//                 .collect(),
//         };

//         events.push(event);
//     }

//     events
// }

// #[derive(Copy, Clone, Debug, sqlx::FromRow)]
// struct TxId(i64);

// async fn tx_id_by_hash(pool: &PgPool, hash: &str) -> Result<TxId, ReportError> {
//     let tx_id = sqlx::query_scalar(
//             "SELECT tx_id FROM event_attributes WHERE type = 'tx' AND composite_key = 'tx.hash' AND value = $1 LIMIT 1"
//         )
//         .bind(hash)
//         .fetch_one(pool)
//         .await
//         .wrap_err("tx_id_by_hash query failed")?;

//     Ok(TxId(tx_id))
// }

// async fn tx_events_by_id(pool: &PgPool, id: TxId) -> Result<Vec<EventAttribute>, ReportError> {
//     let events = sqlx::query_as("SELECT type,key,value FROM Event_attributes WHERE tx_id = $1")
//         .bind(id.0)
//         .fetch_all(pool)
//         .await
//         .wrap_err("tx_events_by_id query failed")?;

//     Ok(events)
// }

// async fn tx_events_by_hash(pool: &PgPool, hash: &str) -> Result<Vec<EventAttribute>, ReportError> {
//     let tx_id = tx_id_by_hash(pool, hash).await?;
//     tx_events_by_id(pool, tx_id).await
// }
