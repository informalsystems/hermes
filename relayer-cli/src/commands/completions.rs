use crate::entry::EntryPoint;
use abscissa_core::clap::Parser;
use abscissa_core::Runnable;
use clap::IntoApp;
use clap_complete::Shell;
use std::io;

#[derive(Debug, Parser)]
pub struct CompletionsCmd {
    #[clap(arg_enum)]
    shell: Shell,
}

impl Runnable for CompletionsCmd {
    fn run(&self) {
        let mut app = EntryPoint::command();
        let app_name = app.get_name().to_owned();
        clap_complete::generate(self.shell, &mut app, app_name, &mut io::stdout());
    }
}
