use std::path::PathBuf;

use git2::build::RepoBuilder;

use argh::FromArgs;

#[derive(Debug, FromArgs)]
#[argh(subcommand, name = "clone-sdk")]
/// Clone
pub struct CloneCmd {
    #[argh(option, short = 'b')]
    /// branch to checkout
    branch: Option<String>,
    /// where to checkout the repository
    #[argh(positional)]
    path: PathBuf,
}

impl CloneCmd {
    pub fn run(&self) {
        if self.path.exists() {
            println!(
                "[info ] Found Cosmos SDK source at '{}'",
                self.path.display()
            );
        } else {
            println!("[info ] Cloning cosmos/cosmos-sdk repository...");

            let url = "https://github.com/cosmos/cosmos-sdk";
            let mut builder = RepoBuilder::new();

            if let Some(branch) = &self.branch {
                println!("[info ] Will check out branch '{}'", branch);
                builder.branch(branch);
            }

            let _repo = builder.clone(url, &self.path).unwrap();

            println!("[info ] => Cloned at '{}'", self.path.display());
        }
    }
}
