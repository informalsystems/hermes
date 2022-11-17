use std::collections::HashMap;

use clap::Parser;
use futures::future::try_join_all;
use itertools::Itertools;
use tracing::{error, info};
use tracing_subscriber::{filter::LevelFilter, EnvFilter};

use tendermint_rpc::{
    abci::{self, tag::Tag},
    endpoint::block_results,
    query::{Condition, Query},
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

async fn run() -> Result<(), Box<dyn std::error::Error>> {
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
        result.total_count,
        heights.iter().join(", ")
    );

    let results = try_join_all(heights.iter().map(|&h| client.block_results(h))).await?;

    for result in results {
        let height = result.height;
        let events = collect_events(result, &query);

        if !events.is_empty() {
            info!("Block {}: found {} matching events", height, events.len());
            info!("{:#?}", events);
        } else {
            info!("Block {}: found no matching events", height);
        }
    }

    Ok(())
}

fn collect_events(res: block_results::Response, query: &Query) -> Vec<abci::Event> {
    let tx_events = res
        .txs_results
        .unwrap_or_default()
        .into_iter()
        .flat_map(|tx| tx.events);

    let begin_events = res.begin_block_events.unwrap_or_default().into_iter();
    let end_events = res.end_block_events.unwrap_or_default().into_iter();

    begin_events
        .chain(tx_events)
        .chain(end_events)
        .filter(|event| event_matches(event, query))
        .collect_vec()
}

fn event_matches(event: &abci::Event, query: &Query) -> bool {
    let tags = attrs_to_map(&event.attributes, &event.type_str);

    query.conditions.iter().all(|cond| {
        tags.get(key(cond))
            .map(|tag| eval(cond, tag))
            .unwrap_or(false)
    })
}

fn key(cond: &Condition) -> &str {
    use Condition::*;

    match cond {
        Eq(k, _) => k,
        Lt(k, _) => k,
        Lte(k, _) => k,
        Gt(k, _) => k,
        Gte(k, _) => k,
        Contains(k, _) => k,
        Exists(k) => k,
    }
}

fn attrs_to_map(tags: &[Tag], type_str: &str) -> HashMap<String, Tag> {
    tags.iter()
        .map(|tag| (format!("{}.{}", type_str, tag.key), tag.clone()))
        .collect()
}

#[allow(unused_variables)]
fn eval(cond: &Condition, tag: &Tag) -> bool {
    use Condition::*;

    match cond {
        Eq(key, op) => tag.value.as_ref() == op.to_string().as_str().trim_matches('\''), // FIXME: Unescape properly
        Contains(key, needle) => tag.value.as_ref().contains(needle),
        Exists(key) => true,
        Lt(key, op) => todo!(),
        Lte(key, op) => todo!(),
        Gt(key, op) => todo!(),
        Gte(key, op) => todo!(),
    }
}
