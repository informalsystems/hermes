//! Definition of the application, based on the Abscissa framework

use std::{
    path::PathBuf,
    thread,
};

use abscissa_core::{
    application::{
        self,
        AppCell,
    },
    component::Component,
    config::{
        self,
        CfgCell,
    },
    terminal::{
        component::Terminal,
        ColorChoice,
    },
    Application,
    Configurable,
    FrameworkError,
    FrameworkErrorKind,
    StandardPaths,
};
use ibc_relayer::{
    config::{
        Config,
        TracingServerConfig,
    },
    util::debug_section::DebugSection,
};

use crate::{
    commands::CliCmd,
    components::{
        JsonTracing,
        PrettyTracing,
    },
    entry::EntryPoint,
    tracing_handle::{
        spawn_reload_handler,
        ReloadHandle,
    },
};

/// Application state
pub static APPLICATION: AppCell<CliApp> = AppCell::new();

/// Obtain a read-only (multi-reader) lock on the application state.
///
/// Panics if the application state has not been initialized.
pub fn app_reader() -> &'static CliApp {
    &APPLICATION
}

/// Obtain a read-only (multi-reader) lock on the application configuration.
///
/// Panics if the application configuration has not been loaded.
pub fn app_config() -> config::Reader<Config> {
    APPLICATION.config.read()
}

/// Cli Application
#[derive(Debug)]
pub struct CliApp {
    /// Application configuration.
    config: CfgCell<Config>,

    /// Application state.
    state: application::State<Self>,

    /// Toggle json output on/off. Changed with the global config option `-j` / `--json`.
    json_output: bool,

    /// Enable the given debug sections.
    debug_sections: Vec<DebugSection>,

    /// Path to the config file.
    config_path: Option<PathBuf>,
}

/// Initialize a new application instance.
///
/// By default no configuration is loaded, and the framework state is
/// initialized to a default, empty state (no components, threads, etc).
impl Default for CliApp {
    fn default() -> Self {
        Self {
            config: CfgCell::default(),
            state: application::State::default(),
            json_output: false,
            debug_sections: Vec::default(),
            config_path: None,
        }
    }
}

impl CliApp {
    /// Whether or not JSON output is enabled
    pub fn json_output(&self) -> bool {
        self.json_output
    }

    /// Returns the enabled debug sections
    pub fn debug_sections(&self) -> &[DebugSection] {
        &self.debug_sections
    }

    /// Returns `true` if the given debug section is enabled
    pub fn debug_enabled(&self, section: DebugSection) -> bool {
        self.debug_sections.contains(&section)
    }

    /// Returns the path to the configuration file
    pub fn config_path(&self) -> Option<&PathBuf> {
        self.config_path.as_ref()
    }
}

impl Application for CliApp {
    /// Entrypoint command for this application.
    type Cmd = EntryPoint;

    /// Application configuration.
    type Cfg = Config;

    /// Paths to resources within the application.
    type Paths = StandardPaths;

    /// Accessor for application configuration.
    fn config(&self) -> config::Reader<Config> {
        self.config.read()
    }

    /// Borrow the application state immutably.
    fn state(&self) -> &application::State<Self> {
        &self.state
    }

    /// Register all components used by this application.
    ///
    /// If you would like to add additional components to your application
    /// beyond the default ones provided by the framework, this is the place
    /// to do so.
    fn register_components(&mut self, command: &Self::Cmd) -> Result<(), FrameworkError> {
        let framework_components = self.framework_components(command)?;
        let mut app_components = self.state.components_mut();
        app_components.register(framework_components)
    }

    /// Post-configuration lifecycle callback.
    ///
    /// Called regardless of whether config is loaded to indicate this is the
    /// time in app lifecycle when configuration would be loaded if
    /// possible.
    fn after_config(&mut self, config: Self::Cfg) -> Result<(), FrameworkError> {
        use ibc_relayer::config::Diagnostic;

        // Configure components
        let mut components = self.state.components_mut();
        components.after_config(&config)?;

        if let Err(diagnostic) = config.validate_config() {
            match diagnostic {
                Diagnostic::Warning(e) => {
                    tracing::warn!("relayer may be misconfigured: {}", e);
                }
                Diagnostic::Error(e) => {
                    return Err(FrameworkErrorKind::ConfigError.context(e).into());
                }
            }
        };

        tracing::info!("running Hermes v{}", clap::crate_version!());

        self.config.set_once(config);

        Ok(())
    }

    /// Overrides the default abscissa components, so that we can setup tracing on our own. See
    /// also `register_components`.
    fn framework_components(
        &mut self,
        command: &Self::Cmd,
    ) -> Result<Vec<Box<dyn Component<Self>>>, FrameworkError> {
        let terminal = Terminal::new(self.term_colors(command));

        let config_path = command.config_path();
        self.config_path = config_path.clone();

        let config = config_path
            .map(|path| self.load_config(&path))
            .transpose()
            .map_err(|err| {
                let path = self.config_path.clone().unwrap_or_default();
                eprintln!(
                    "The Hermes configuration file at path '{}' is invalid, reason: {}",
                    path.to_string_lossy(),
                    err
                );
                eprintln!(
                    "Please see the example configuration for detailed information about the \
                    supported configuration options: \
                    https://github.com/informalsystems/hermes/blob/master/config.toml"
                );
                std::process::exit(1);
            })
            .expect("invalid config")
            .unwrap_or_default();

        // Update the `json_output` flag used by `conclude::Output`
        self.json_output = command.json;

        // Update the `debug_sections` flag
        self.debug_sections = command.debug.iter().copied().map(Into::into).collect();

        // Enable profiling if requested
        let enable_console = self.debug_enabled(DebugSection::Profiling);
        let enable_json = self.debug_enabled(DebugSection::ProfilingJson);
        ibc_relayer::util::profiling::enable(enable_console, enable_json);

        let is_start_cmd = command
            .command
            .as_ref()
            .map_or(false, |cmd| matches!(cmd, CliCmd::Start(_)));

        if command.json {
            // Enable JSON by using the crate-level `Tracing`
            let tracing = JsonTracing::new(config.global, &self.debug_sections)?;
            Ok(vec![Box::new(terminal), Box::new(tracing)])
        } else {
            // Use abscissa's tracing, which pretty-prints to the terminal obeying log levels
            let (tracing, reload_handle) =
                PrettyTracing::new_with_reload_handle(config.global, &self.debug_sections)?;

            if is_start_cmd {
                spawn_tracing_reload_server(reload_handle, config.tracing_server.clone());
            }

            Ok(vec![Box::new(terminal), Box::new(tracing)])
        }
    }

    // Disable color support due to
    // https://github.com/iqlusioninc/abscissa/issues/589
    fn term_colors(&self, _command: &Self::Cmd) -> ColorChoice {
        ColorChoice::Never
    }
}

fn spawn_tracing_reload_server<S: 'static>(
    reload_handle: ReloadHandle<S>,
    config: TracingServerConfig,
) {
    thread::spawn(move || {
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();

        let result = rt.block_on(spawn_reload_handler(reload_handle, config));

        if let Err(e) = result {
            eprintln!("ERROR: failed to spawn tracing reload handler: {e}");
        }
    });
}
