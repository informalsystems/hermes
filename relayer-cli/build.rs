use std::env;
use std::ffi::OsStr;
use std::process::{Command, Output};

fn main() {
    // Overwrites the package `name` to be 'hermes' (the binary name), instead of 'ibc-relayer-cli'
    // (which is the crate name), so that abscissa outputs consistent usage and help messages.
    // https://github.com/informalsystems/ibc-rs/issues/590
    // Note: This can potentially break the normal cargo (or crates.io) workflow.
    println!("cargo:rustc-env=CARGO_PKG_NAME=hermes");

    // Make the version (along with meta) available to the relayer CLI crate
    println!("cargo:rustc-env=HERMES_VERSION={}", version());
}

fn version() -> String {
    let mut vers = env::var("CARGO_PKG_VERSION").unwrap();

    if let Some(git) = GitHandle::new() {
        println!("cargo:rustc-rerun-if-changed=.git/HEAD");

        vers.push('+');
        vers.push_str(&git.branch());
        vers.push('-');
        vers.push_str(&git.last_commit_hash());
        if git.is_dirty() {
            vers.push_str("-dirty");
        }
    }

    vers.replace("\n", "")
}

struct GitHandle;

impl GitHandle {
    pub fn new() -> Option<Self> {
        if Self::is_git_repo() {
            Some(GitHandle)
        } else {
            None
        }
    }

    // Returns the current branch as a string - if the branch name has a '/' returns part after the
    // last '/'
    pub fn branch(&self) -> String {
        let branch = Self::command(&["rev-parse", "--abbrev-ref", "HEAD"]);
        let branch_str = String::from_utf8_lossy(&branch.stdout);
        branch_str
            .contains('/')
            .then(|| {
                branch_str
                    .split('/')
                    .collect::<Vec<&str>>()
                    .last()
                    .unwrap()
                    .to_string()
            })
            .unwrap_or_else(|| branch_str.into())
    }

    // Returns the short hash of the last git commit
    pub fn last_commit_hash(&self) -> String {
        let commit = Self::command(&["rev-parse", "--short", "HEAD"]);
        String::from_utf8_lossy(&commit.stdout).into_owned()
    }

    // Checks if the git repo is dirty
    pub fn is_dirty(&self) -> bool {
        Self::command(&["status", "--porcelain"]).status.success()
    }

    #[inline]
    fn command(args: impl IntoIterator<Item = impl AsRef<OsStr>>) -> Output {
        Command::new("git").args(args).output().unwrap()
    }

    // returns true iff git is installed and current directory is a git repo
    fn is_git_repo() -> bool {
        Command::new("git")
            .args(&["rev-parse", "--git-dir"])
            .output()
            .map_or(false, |o| o.status.success())
    }
}
