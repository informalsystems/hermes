use std::{path::PathBuf, process};

use git2::Repository;

use argh::FromArgs;

#[derive(Debug, FromArgs)]
#[argh(subcommand, name = "clone-sdk")]
/// Clone
pub struct CloneCmd {
    /// commit to checkout
    #[argh(option, short = 'c')]
    commit: Option<String>,
    /// where to checkout the repository
    #[argh(option, short = 'o')]
    path: PathBuf,
}

impl CloneCmd {
    pub fn run(&self) {
        let repo = if self.path.exists() {
            println!(
                "[info ] Found Cosmos SDK source at '{}'",
                self.path.display()
            );

            Repository::open(&self.path).unwrap_or_else(|e| {
                println!("[error] Failed to open repository: {}", e);
                process::exit(1)
            })
        } else {
            println!("[info ] Cloning cosmos/cosmos-sdk repository...");

            let url = "https://github.com/cosmos/cosmos-sdk";

            Repository::clone(url, &self.path).unwrap_or_else(|e| {
                println!("[error] Failed to clone the repository: {}", e);
                process::exit(1)
            })
        };

        if let Some(ref commit) = self.commit {
            let treeish = format!("refs/heads/{}", commit);
            repo.set_head(&treeish).unwrap_or_else(|e| {
                println!("[error] Failed to set HEAD to {}: {}", commit, e);
                process::exit(1)
            });

            println!("[info ] HEAD is at {}", commit);
        }

        println!("[info ] Cloned at '{}'", self.path.display());
    }
}
