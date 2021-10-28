use eyre::Report as Error;
use tracing_subscriber::{
    self as ts,
    filter::EnvFilter,
    layer::{Layer, SubscriberExt},
    util::SubscriberInitExt,
};

pub fn init_test() -> Result<(), Error> {
    color_eyre::install()?;

    let env_filter = EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("debug"));

    let module_filter_fn = ts::filter::filter_fn(|metadata| match metadata.module_path() {
        Some(path) => path.starts_with("ibc"),
        None => false,
    });

    let module_filter = ts::fmt::layer().with_filter(module_filter_fn);

    ts::registry().with(env_filter).with(module_filter).init();

    Ok(())
}
