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

    /// tag to checkout
    #[argh(option, short = 't')]
    tag: Option<String>,

    /// where to checkout the repository
    #[argh(option, short = 'o')]
    out: PathBuf,
}

impl CloneCmd {
    pub fn validate(&self) {
        if self.commit.is_some() && self.tag.is_some() {
            println!("[error] The --commit and --tag options are mutually exclusive.");
            process::exit(1);
        }
    }

    pub fn run(&self) {
        self.validate();

        let repo = if self.out.exists() {
            println!(
                "[info ] Found Cosmos SDK source at '{}'",
                self.out.display()
            );

            Repository::open(&self.out).unwrap_or_else(|e| {
                println!("[error] Failed to open repository: {}", e);
                process::exit(1)
            })
        } else {
            println!("[info ] Cloning cosmos/cosmos-sdk repository...");

            let url = "https://github.com/cosmos/cosmos-sdk";

            let repo = Repository::clone(url, &self.out).unwrap_or_else(|e| {
                println!("[error] Failed to clone the repository: {}", e);
                process::exit(1)
            });

            println!("[info ] Cloned at '{}'", self.out.display());

            repo
        };

        if let Some(ref rev) = self.commit {
            checkout_commit(&repo, rev).unwrap_or_else(|e| {
                println!("[error] Failed to checkout commit {}: {}", rev, e);
                process::exit(1)
            });
        } else if let Some(ref tag) = self.tag {
            checkout_tag(&repo, tag).unwrap_or_else(|e| {
                println!("[error] Failed to checkout tag {}: {}", tag, e);
                process::exit(1)
            });
        }
    }
}

fn checkout_commit(repo: &Repository, rev: &str) -> Result<(), git2::Error> {
    let oid = Oid::from_str(rev)?;
    let commit = repo.find_commit(oid)?;

    // Create a new branch `rev` that points to `commit`
    repo.branch(rev, &commit, true)?;

    // Checkout the newly created branch
    let treeish = format!("refs/heads/{}", rev);
    let object = repo.revparse_single(&treeish)?;
    repo.checkout_tree(&object, None)?;
    repo.set_head(&treeish)?;

    println!("[info ] Checked out commit {}", rev);

    Ok(())
}

fn checkout_tag(repo: &Repository, tag_name: &str) -> Result<(), git2::Error> {
    // Find a tag with name `tag_name`
    let tag = repo
        .references()?
        .into_iter()
        .flatten()
        .filter(|r| r.is_tag())
        .flat_map(|r| r.peel_to_tag())
        .find(|t| t.name() == Some(tag_name));

    if let Some(tag) = tag {
        // Get the commit this tag points to
        let target_oid = tag.target()?.id();
        let commit = repo.find_commit(target_oid)?;

        // Create a new branch `tag_name` that points to `commit`
        repo.branch(tag_name, &commit, true)?;

        // Checkout the newly created branch
        let rev = format!("refs/heads/{}", tag_name);
        let obj = repo.revparse_single(&rev)?;
        repo.checkout_tree(&obj, None)?;
        repo.set_head(&rev)?;

        println!("[info ] Checked out tag {}", tag_name);
    } else {
        println!("[error] Could not find tag {}", tag_name);
        process::exit(1);
    }

    Ok(())
}
