//! Cli Abscissa Application

use abscissa_core::terminal::component::Terminal;
use abscissa_core::{
    application::{self, AppCell},
    component::Component,
    config, Application, Configurable, FrameworkError, FrameworkErrorKind, StandardPaths,
};
use ibc_relayer::config::Config;

use crate::components::{JsonTracing, PrettyTracing};
use crate::entry::EntryPoint;
use crate::{commands::CliCmd, config::validate_config};

/// Application state
pub static APPLICATION: AppCell<CliApp> = AppCell::new();

/// Obtain a read-only (multi-reader) lock on the application state.
///
/// Panics if the application state has not been initialized.
pub fn app_reader() -> application::lock::Reader<CliApp> {
    APPLICATION.read()
}

/// Obtain an exclusive mutable lock on the application state.
pub fn app_writer() -> application::lock::Writer<CliApp> {
    APPLICATION.write()
}

/// Obtain a read-only (multi-reader) lock on the application configuration.
///
/// Panics if the application configuration has not been loaded.
pub fn app_config() -> config::Reader<CliApp> {
    config::Reader::new(&APPLICATION)
}

/// Cli Application
#[derive(Debug)]
pub struct CliApp {
    /// Application configuration.
    config: Option<Config>,

    /// Application state.
    state: application::State<Self>,

    /// Toggle json output on/off. Changed with the global config option `-j` / `--json`.
    json_output: bool,
}

/// Initialize a new application instance.
///
/// By default no configuration is loaded, and the framework state is
/// initialized to a default, empty state (no components, threads, etc).
impl Default for CliApp {
    fn default() -> Self {
        Self {
            config: None,
            state: application::State::default(),
            json_output: false,
        }
    }
}

impl CliApp {
    /// Whether or not JSON output is enabled
    pub fn json_output(&self) -> bool {
        self.json_output
    }
}

impl Application for CliApp {
    /// Entrypoint command for this application.
    type Cmd = EntryPoint<CliCmd>;

    /// Application configuration.
    type Cfg = Config;

    /// Paths to resources within the application.
    type Paths = StandardPaths;

    /// Accessor for application configuration.
    fn config(&self) -> &Config {
        self.config.as_ref().expect("config not loaded")
    }

    /// Borrow the application state immutably.
    fn state(&self) -> &application::State<Self> {
        &self.state
    }

    /// Borrow the application state mutably.
    fn state_mut(&mut self) -> &mut application::State<Self> {
        &mut self.state
    }

    /// Register all components used by this application.
    ///
    /// If you would like to add additional components to your application
    /// beyond the default ones provided by the framework, this is the place
    /// to do so.
    fn register_components(&mut self, command: &Self::Cmd) -> Result<(), FrameworkError> {
        let components = self.framework_components(command)?;
        self.state.components.register(components)
    }

    /// Post-configuration lifecycle callback.
    ///
    /// Called regardless of whether config is loaded to indicate this is the
    /// time in app lifecycle when configuration would be loaded if
    /// possible.
    fn after_config(&mut self, config: Self::Cfg) -> Result<(), FrameworkError> {
        // Configure components
        self.state.components.after_config(&config)?;

        validate_config(&config)
            .map_err(|validation_err| FrameworkErrorKind::ConfigError.context(validation_err))?;
        self.config = Some(config);

        Ok(())
    }

    /// Overrides the default abscissa components, so that we can setup tracing on our own. See
    /// also `register_components`.
    fn framework_components(
        &mut self,
        command: &Self::Cmd,
    ) -> Result<Vec<Box<dyn Component<Self>>>, FrameworkError> {
        let terminal = Terminal::new(self.term_colors(command));

        let config = command
            .config_path()
            .map(|path| self.load_config(&path))
            .transpose()?
            .unwrap_or_default();

        // Update the `json_output` flag used by `conclude::Output`
        self.json_output = command.json;

        if command.json {
            // Enable JSON by using the crate-level `Tracing`
            let tracing = JsonTracing::new(config.global)?;
            Ok(vec![Box::new(terminal), Box::new(tracing)])
        } else {
            // Use abscissa's tracing, which pretty-prints to the terminal obeying log levels
            let tracing = PrettyTracing::new(config.global)?;
            Ok(vec![Box::new(terminal), Box::new(tracing)])
        }
    }
}
