use std::path::PathBuf;

use abscissa_core::command::Usage;
use abscissa_core::{Command, Config, Configurable, FrameworkError, Options, Runnable};

/// Custom entry point for Hermes.
///
/// Replaces `abscissa_core::EntryPoint` with custom-made flag (for JSON output).
#[derive(Debug, Options)]
pub struct EntryPoint<Cmd>
where
    Cmd: Command + Runnable,
{
    /// Path to the configuration file
    #[options(short = "c", help = "path to configuration file")]
    pub config: Option<PathBuf>,

    /// Toggle JSON output mode one verbosity setting
    #[options(short = "j", help = "enable JSON output")]
    pub json: bool,

    /// Subcommand to execute.
    ///
    /// The `command` option will delegate option parsing to the command type,
    /// starting at the first free argument.
    #[options(command)]
    pub command: Option<Cmd>,
}

impl<Cmd> EntryPoint<Cmd>
where
    Cmd: Command + Runnable,
{
    /// Borrow the underlying command type or print usage info and exit
    fn command(&self) -> &Cmd {
        self.command
            .as_ref()
            .unwrap_or_else(|| Cmd::print_usage_and_exit(&[]))
    }
}

impl<Cmd> Runnable for EntryPoint<Cmd>
where
    Cmd: Command + Runnable,
{
    fn run(&self) {
        self.command().run()
    }
}

impl<Cmd> Command for EntryPoint<Cmd>
where
    Cmd: Command + Runnable,
{
    /// Name of this program as a string
    fn name() -> &'static str {
        "hermes"
    }

    /// Description of this program.
    /// Used whenever a command's usage is printed
    /// (i.e., after the user invoked a command wrongly).
    ///
    /// Note:
    ///     Any new line or extra white spaces in the returned &str
    ///     here will be trimmed (see `Usage`), so the returned
    ///     &str should be a concise one-liner help message.
    fn description() -> &'static str {
        r#"
        For help, run `hermes [<FLAGS>] help <COMMAND>`, for example: `hermes help create client`
        "#
    }

    /// Version of this program
    fn version() -> &'static str {
        Cmd::version()
    }

    /// Authors of this program
    fn authors() -> &'static str {
        Cmd::authors()
    }

    /// Get usage information for a particular subcommand (if available)
    fn subcommand_usage(command: &str) -> Option<Usage> {
        Cmd::subcommand_usage(command)
    }
}

impl<Cfg, Cmd> Configurable<Cfg> for EntryPoint<Cmd>
where
    Cmd: Command + Configurable<Cfg> + Runnable,
    Cfg: Config,
{
    /// Path to the command's configuration file
    fn config_path(&self) -> Option<PathBuf> {
        match &self.config {
            // Use explicit `-c`/`--config` argument if passed
            Some(cfg) => Some(cfg.clone()),

            // Otherwise defer to the toplevel command's config path logic
            None => self.command.as_ref().and_then(|cmd| cmd.config_path()),
        }
    }

    /// Process the configuration after it has been loaded, potentially
    /// modifying it or returning an error if options are incompatible
    fn process_config(&self, config: Cfg) -> Result<Cfg, FrameworkError> {
        match &self.command {
            Some(cmd) => cmd.process_config(config),
            None => Ok(config),
        }
    }
}
