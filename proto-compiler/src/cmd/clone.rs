use std::{path::PathBuf, process};

use git2::{Oid, Repository};

use argh::FromArgs;

#[derive(Debug, FromArgs)]
#[argh(subcommand, name = "clone")]
/// Clone
pub struct CloneCmd {
    /// commit to checkout for the SDK repo
    #[argh(option, short = 'c')]
    sdk_commit: Option<String>,

    /// tag to checkout for the IBC-go repo
    #[argh(option, short = 't')]
    sdk_tag: Option<String>,

    /// commit to checkout
    #[argh(option, short = 'i')]
    ibc_go_commit: String,

    /// where to checkout the repository
    #[argh(option, short = 'o')]
    out: PathBuf,
}

impl CloneCmd {
    pub fn validate(&self) {
        if self.sdk_commit.is_some() && self.sdk_tag.is_some() {
            println!("[error] The --sdk-commit and --sdk-tag options are mutually exclusive.");
            process::exit(1);
        }
    }

    pub fn sdk_subdir(&self) -> PathBuf {
        let mut sdk_path = self.out.clone();
        sdk_path.push("sdk/");
        sdk_path
    }

    pub fn ibc_subdir(&self) -> PathBuf {
        let mut ibc_path = self.out.clone();
        ibc_path.push("ibc/");
        ibc_path
    }

    pub fn run(&self) {
        self.validate();

        let sdk_repo = if self.out.exists() {
            println!(
                "[info ] Found Cosmos SDK or IBC proto source at '{}'",
                self.out.display()
            );

            Repository::open(&self.out).unwrap_or_else(|e| {
                println!("[error] Failed to open repository: {}", e);
                process::exit(1)
            })
        } else {
            println!("[info ] Cloning cosmos/cosmos-sdk repository...");

            let url = "https://github.com/cosmos/cosmos-sdk";

            let repo = Repository::clone(url, &self.sdk_subdir()).unwrap_or_else(|e| {
                println!("[error] Failed to clone the SDK repository: {}", e);
                process::exit(1)
            });

            println!("[info ] Cloned at '{}'", self.sdk_subdir().display());

            repo
        };

        if let Some(ref rev) = self.sdk_commit {
            checkout_commit(&sdk_repo, rev).unwrap_or_else(|e| {
                println!("[error] Failed to checkout SDK commit {}: {}", rev, e);
                process::exit(1)
            });
        } else if let Some(ref tag) = self.sdk_tag {
            checkout_tag(&sdk_repo, tag).unwrap_or_else(|e| {
                println!("[error] Failed to checkout SDK tag {}: {}", tag, e);
                process::exit(1)
            });
        }

        println!("[info ] Cloning cosmos/ibc-go repository...");

        let ibc_url = "https://github.com/cosmos/ibc-go";

        let ibc_repo = Repository::clone(ibc_url, &self.ibc_subdir()).unwrap_or_else(|e| {
            println!("[error] Failed to clone the IBC repository: {}", e);
            process::exit(1)
        });

        println!("[info ] Cloned at '{}'", self.ibc_subdir().display());
        checkout_commit(&ibc_repo, &self.ibc_go_commit).unwrap_or_else(|e| {
            println!(
                "[error] Failed to checkout IBC commit {}: {}",
                self.ibc_go_commit, e
            );
            process::exit(1)
        });
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
