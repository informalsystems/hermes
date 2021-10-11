use eyre::Report as Error;

pub fn init_test() -> Result<(), Error> {
    color_eyre::install()?;
    tracing_subscriber::fmt::init();

    Ok(())
}
