use crate::entry::EntryPoint;
use abscissa_core::clap::Parser;
use abscissa_core::Runnable;
use clap::IntoApp;
use clap_complete::Shell;
use std::io;

#[derive(Debug, Parser, PartialEq, Eq)]
pub struct CompletionsCmd {
    #[clap(
        long = "shell",
        value_name = "SHELL",
        arg_enum,
        help_heading = "REQUIRED"
    )]
    shell: Shell,
}

impl Runnable for CompletionsCmd {
    fn run(&self) {
        let mut app = EntryPoint::command();
        let app_name = app.get_name().to_owned();
        clap_complete::generate(self.shell, &mut app, app_name, &mut io::stdout());
    }
}

#[cfg(test)]
mod tests {
    use super::CompletionsCmd;

    use abscissa_core::clap::Parser;
    use clap_complete::Shell;

    #[test]
    fn test_completions() {
        assert_eq!(
            CompletionsCmd { shell: Shell::Zsh },
            CompletionsCmd::parse_from(["test", "--shell", "zsh"])
        )
    }

    #[test]
    fn test_completions_no_shell() {
        assert!(CompletionsCmd::try_parse_from(["test", "--shell"]).is_err())
    }

    #[test]
    fn test_completions_no_shell_flag() {
        assert!(CompletionsCmd::try_parse_from(["test"]).is_err())
    }

    #[test]
    fn test_completions_unknown_shell() {
        assert!(CompletionsCmd::try_parse_from(["test", "--shell", "my_shell"]).is_err())
    }
}
