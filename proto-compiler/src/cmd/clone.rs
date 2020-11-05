use std::{path::PathBuf, process};

use git2::{Oid, Repository};

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

        if let Some(ref rev) = self.commit {
            checkout_commit(&repo, rev).unwrap_or_else(|e| {
                println!("[error] Failed to checkout {}: {}", rev, e);
                process::exit(1)
            });

            println!("[info ] HEAD is at {}", rev);
        }

        println!("[info ] Cloned at '{}'", self.path.display());
    }
}

fn checkout_commit(repo: &Repository, rev: &str) -> Result<(), git2::Error> {
    let oid = Oid::from_str(rev)?;
    let commit = repo.find_commit(oid)?;
    repo.branch(rev, &commit, false)?;

    let treeish = format!("refs/heads/{}", rev);
    let object = repo.revparse_single(&treeish)?;

    repo.checkout_tree(&object, None)?;
    repo.set_head(&treeish)?;

    Ok(())
}
