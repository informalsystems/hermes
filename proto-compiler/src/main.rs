use argh::FromArgs;

mod cmd;
use cmd::clone::CloneCmd;
use cmd::compile_std;
use cmd::compile_no_std;

#[derive(Debug, FromArgs)]
/// App
struct App {
    #[argh(subcommand)]
    cmd: Command,
}

#[derive(Debug, FromArgs)]
#[argh(subcommand)]
enum Command {
    Clone(CloneCmd),
    CompileStd(compile_std::CompileCmd),
    CompileNoStd(compile_no_std::CompileCmd),
}

fn main() {
    let app: App = argh::from_env();

    match app.cmd {
        Command::Clone(clone) => clone.run(),
        Command::CompileStd(compile) => compile.run(),
        Command::CompileNoStd(compile) => compile.run(),
    }
}
