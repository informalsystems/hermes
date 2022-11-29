use std::collections::HashMap;

use clap::Parser;
use futures::future::try_join_all;
use itertools::Itertools;
use tracing::{error, info};
use tracing_subscriber::{filter::LevelFilter, EnvFilter};

use tendermint::abci::{Event, EventAttribute};
use tendermint_rpc::{
    endpoint::block_results,
    query::{Condition, Operand, Operation, Query},
    Client, HttpClient, Order, Url,
};

#[derive(Debug, Parser)]
struct Opts {
    /// The URL of the Tendermint node's RPC endpoint
    #[clap(short, long)]
    url: Url,

    /// The query against which blocks should be matched
    query: Query,

    /// The maximum height at which blocks should be queried (optional)
    #[clap(long)]
    max_height: Option<u64>,

    /// Which page to get
    #[clap(long, default_value = "1")]
    page: u32,

    /// How many results per page
    #[clap(long, default_value = "10")]
    per_page: u8,

    /// How to order the results by height
    #[clap(long, default_value = "desc")]
    order: Order,

    /// Enable verbose mode, display partially matching events
    #[clap(short, long)]
    verbose: bool,
}

#[tokio::main(flavor = "current_thread")]
async fn main() {
    tracing_subscriber::fmt()
        .with_env_filter(
            EnvFilter::builder()
                .with_default_directive(LevelFilter::INFO.into())
                .from_env_lossy(),
        )
        .init();

    match run().await {
        Ok(()) => info!("SUCCESS"),
        Err(e) => error!("{e}"),
    }
}

type BoxError = Box<dyn std::error::Error>;

async fn run() -> Result<(), BoxError> {
    let opts = Opts::parse();

    info!("Connecting to {}", opts.url);
    let client = HttpClient::new(opts.url).unwrap();

    let query = opts.query.clone();

    info!("Searching for blocks");
    let result = client
        .block_search(opts.query, opts.page, opts.per_page, opts.order)
        .await?;

    let heights = result
        .blocks
        .iter()
        .map(|b| b.block.header.height)
        .filter(|h| opts.max_height.map_or(true, |max| h.value() <= max))
        .collect_vec();

    info!(
        "Found {} blocks with partially matching events at heights: {}",
        heights.len(),
        heights.iter().join(", ")
    );

    let results = try_join_all(heights.iter().map(|&h| client.block_results(h))).await?;

    if opts.verbose {
        for result in &results {
            let height = result.height;
            let events = collect_events(result.clone()).collect_vec();

            if !events.is_empty() {
                info!(
                    "Block {}: found {} partially matching events",
                    height,
                    events.len()
                );
                info!("{:#?}", events);
            } else {
                info!(
                    "Block {}: found no matching events, even with partial match",
                    height
                );
            }
        }
    }

    for result in results {
        let height = result.height;
        let events = collect_events(result)
            .filter(|event| event_matches(event, &query))
            .collect_vec();

        if !events.is_empty() {
            info!("Block {}: found {} matching events", height, events.len());
            info!("{:#?}", events);
        } else {
            info!("Block {}: found no matching events", height);
        }
    }

    Ok(())
}

fn collect_events(res: block_results::Response) -> impl Iterator<Item = Event> {
    let tx_events = res
        .txs_results
        .unwrap_or_default()
        .into_iter()
        .flat_map(|tx| tx.events);

    let begin_events = res.begin_block_events.unwrap_or_default().into_iter();
    let end_events = res.end_block_events.unwrap_or_default().into_iter();

    begin_events.chain(tx_events).chain(end_events)
}

fn event_matches(event: &Event, query: &Query) -> bool {
    let tags = attrs_to_map(&event.attributes, &event.kind);

    query.conditions.iter().all(|cond| {
        tags.get(&cond.key)
            .map(|tag| {
                eval(cond, tag).unwrap_or_else(|e| {
                    error!("error when evaluating query: {}", e);
                    false
                })
            })
            .unwrap_or(false)
    })
}

fn attrs_to_map(attrs: &[EventAttribute], kind: &str) -> HashMap<String, EventAttribute> {
    attrs
        .iter()
        .map(|tag| (format!("{}.{}", kind, tag.key), tag.clone()))
        .collect()
}

macro_rules! eval_op {
    ($attr:expr, $op:tt $rhs:expr) => {
        {
            let lhs = to_matching_operand(&$attr, $rhs)?;
            match (&lhs, $rhs) {
                (Operand::String(l), Operand::String(r)) => Ok(l $op r),
                (Operand::Signed(l), Operand::Signed(r)) => Ok(l $op r),
                (Operand::Unsigned(l), Operand::Unsigned(r)) => Ok(l $op r),
                (Operand::Float(l), Operand::Float(r)) => Ok(l $op r),
                (Operand::Date(l), Operand::Date(r)) => Ok(l $op r),
                (Operand::DateTime(l), Operand::DateTime(r)) => Ok(l $op r),
                _ => Err("mismatching types".into()),
            }
        }
    }
}

#[allow(unused_variables)]
fn eval(cond: &Condition, attr: &EventAttribute) -> Result<bool, BoxError> {
    match &cond.operation {
        // we know this key exists otherwise we wouldn't have called `eval`
        Operation::Exists => Ok(true),
        Operation::Contains(needle) => Ok(attr.value.contains(needle)),
        Operation::Eq(rhs) => eval_op!(attr.value, == rhs),
        Operation::Lt(rhs) => eval_op!(attr.value, < rhs),
        Operation::Lte(rhs) => eval_op!(attr.value, <= rhs),
        Operation::Gt(rhs) => eval_op!(attr.value, <= rhs),
        Operation::Gte(rhs) => eval_op!(attr.value, <= rhs),
    }
}

fn to_matching_operand(value: &str, op: &Operand) -> Result<Operand, BoxError> {
    match op {
        Operand::String(_) => Ok(Operand::String(value.to_owned())),
        Operand::Signed(_) => value.parse().map(Operand::Signed).map_err(Into::into),
        Operand::Unsigned(_) => value.parse().map(Operand::Unsigned).map_err(Into::into),
        Operand::Float(_) => value.parse().map(Operand::Float).map_err(Into::into),
        Operand::Date(_) => todo!(),
        Operand::DateTime(_) => todo!(),
    }
}
