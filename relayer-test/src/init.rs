use eyre::Report as Error;
use tracing_subscriber::{
    self as ts,
    layer::{Layer, SubscriberExt},
    util::SubscriberInitExt,
};

pub fn init_test() -> Result<(), Error> {
    color_eyre::install()?;

    let filter = ts::filter::filter_fn(|metadata| match metadata.module_path() {
        Some(path) => path.starts_with("ibc"),
        None => false,
    });

    ts::registry()
        .with(ts::fmt::layer().with_filter(filter))
        .init();

    Ok(())
}
