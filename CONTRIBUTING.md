# Contributing

Thank you for your interest in contributing. The goal
of ibc-rs is to provide a high quality, formally verified implementation of
the IBC protocol and relayer.

All work on the code base should be motivated by a Github
Issue. Search is a good place to start when looking for places to contribute.
If you would like to work on an issue which already exists, please indicate so
by leaving a comment. If you'd like to work on something else, open an Issue to
start the discussion.

The rest of this document outlines the best practices for contributing to this
repository:

- [Decision Making](#decision-making) - process for agreeing to changes
- [Forking](#forking) - fork the repo to make pull requests
- [Changelog](#changelog) - changes must be recorded in the changelog
- [Pull Requests](#pull-requests) - what makes a good pull request
- [Releases](#releases) - how to release new version of the crates

## Decision Making

When contributing to the project, the following process leads to the best chance of
landing the changes in master.

All new contributions should start with a Github
Issue. The issue helps capture the problem you're trying to solve and allows for
early feedback. Once the issue is created, maintainers may request more detailed
documentation be written in the form of a Request for Comment (RFC) or
Architectural Decision Record
([ADR](https://github.com/informalsystems/ibc-rs/blob/master/docs/architecture/README.md)).

Discussion at the RFC stage will build collective understanding of the dimensions
of the problems and help structure conversations around trade-offs.

When the problem is well understood but the solution leads to large
structural changes to the code base, these changes should be proposed in
the form of an [Architectural Decision Record
(ADR)](./docs/architecture/). The ADR will help build consensus on an
overall strategy to ensure the code base maintains coherence
in the larger context. If you are not comfortable with writing an ADR,
you can open a less-formal issue and the maintainers will help you
turn it into an ADR.

When the problem as well as proposed solution are well understood,
changes should start with a [draft
pull request](https://github.blog/2019-02-14-introducing-draft-pull-requests/)
against master. The draft signals that work is underway. When the work
is ready for feedback, hitting "Ready for Review" will signal to the
maintainers to take a look.

Implementation trajectories should aim to proceed where possible as a series
of smaller incremental changes, in the form of small PRs that can be merged
quickly. This helps manage the load for reviewers and reduces the likelihood
that PRs will sit open for longer.

![Contributing flow](https://github.com/tendermint/tendermint/blob/v0.33.6/docs/imgs/contributing.png?raw=true)

Each stage of the process is aimed at creating feedback cycles which align contributors and maintainers to make sure:

- Contributors don’t waste their time implementing/proposing features which won’t land in `master`.
- Maintainers have the necessary context in order to support and review contributions.

## Forking

If you do not have write access to the repository, your contribution should be
made through a fork on Github. Fork the repository, contribute to your fork,
and make a pull request back upstream.

When forking, add your fork's URL as a new git remote in your local copy of the
repo. For instance, to create a fork and work on a branch of it:

- Create the fork on GitHub, using the fork button.
- `cd` to the original clone of the repo on your machine
- `git remote rename origin upstream`
- `git remote add origin git@github.com:<location of fork>

Now `origin` refers to your fork and `upstream` refers to this version.
Now `git push -u origin master` to update the fork, and make pull requests against this repo.

To pull in updates from the origin repo, run

- `git fetch upstream`
- `git rebase upstream/master` (or whatever branch you want)

## Changelog

Every non-trivial PR must update the [CHANGELOG](CHANGELOG.md). This is
accomplished indirectly by adding entries to the `.changelog` folder in
[unclog](https://github.com/informalsystems/unclog) format. `CHANGELOG.md` will
be built by whomever is responsible for performing a release just prior to
release - this is to avoid changelog conflicts prior to releases. For example:

### Add a .changelog entry for the `ibc` crate (in the `modules` directory)
### under the `IMPROVEMENTS` section in CHANGELOG.md.

```bash
unclog add -c ibc improvements 1234-some-issue
```

### Add a .changelog entry for the `ibc-relayer-cli` crate (in the `relayer-cli`
### directory) under the `FEATURES` section in CHANGELOG.md.

```bash
unclog add -c ibc-relayer-cli features 1235-some-other-issue
```

### Preview unreleased changes

```bash
unclog build -u
```

The Changelog is *not* a record of what Pull Requests were merged;
the commit history already shows that. The Changelog is a notice to users
about how their expectations of the software should be modified.
It is part of the UX of a release and is a *critical* user facing integration point.
The Changelog must be clean, inviting, and readable, with concise, meaningful entries.
Entries must be semantically meaningful to users. If a change takes multiple
Pull Requests to complete, it should likely have only a single entry in the
Changelog describing the net effect to the user. Instead of linking PRs directly, we
instead prefer to log issues, which tend to be higher-level, hence more relevant for users.

When writing Changelog entries, ensure they are targeting users of the software,
not fellow developers. Developers have much more context and care about more
things than users do. Changelogs are for users.

Changelog structure is modeled after
[Tendermint Core](https://github.com/tendermint/tendermint/blob/master/CHANGELOG.md)
and [Hashicorp Consul](http://github.com/hashicorp/consul/tree/master/CHANGELOG.md).
See those changelogs for examples.

We currently split changes for a given release between these four sections: Breaking
Changes, Features, Improvements, Bug Fixes.

Entries in the changelog should initially be logged in the __Unreleased__ section, which
represents a "staging area" for accumulating all the changes throughout a
release (see [Pull Requests](#pull-requests) below). With each release,
the entries then move from this section into their permanent place under a
specific release number in Changelog.

Changelog entries should be formatted as follows:

```
- [pkg] Some description about the change ([#xxx](https://github.com/informalsystems/ibc-rs/issues/xxx)) (optional @contributor)
```

Here, `pkg` is the part of the code that changed (typically a
top-level crate, but could be <crate>/<module>), `xxx` is the issue number, and `contributor`
is the author/s of the change.

It's also acceptable for `xxx` to refer to the relevant pull request, but issue
numbers are preferred.
Note this means issues (or pull-requests) should be opened first so the changelog can then
be updated with the corresponding number.

Changelog entries should be ordered alphabetically according to the
`pkg`, and numerically according to their issue/PR number.

Changes with multiple classifications should be doubly included (eg. a bug fix
that is also a breaking change should be recorded under both).

Breaking changes are further subdivided according to the APIs/users they impact.
Any change that effects multiple APIs/users should be recorded multiply - for
instance, a change to some core protocol data structure might need to be
reflected both as breaking the core protocol but also breaking any APIs where core data structures are
exposed.

## Pull Requests

The master development branch is `master`.
Branch names should be prefixed with the author, eg. `name/feature-x`.

Pull requests are made against `master`
and are squash merged into master.

PRs must:

- make reference to an issue outlining the context.
- update any relevant documentation and include tests.
- add a corresponding entry in the `.changelog` directory using `unclog`,
  see the section above for more details.

Pull requests should aim to be small and self contained to facilitate quick
review and merging. Larger change sets should be broken up across multiple PRs.
Commits should be concise but informative, and moderately clean. Commits will be squashed into a
single commit for the PR with all the commit messages.

## Releases

Our release process is as follows:

1. Update the [changelog](#changelog) to reflect and summarize all changes in
   the release. This involves:
   1. Running `unclog build -u` and copy pasting the output at the top
      of the `CHANGELOG.md` file, making sure to update the header with
      the new version.
   1. Running `unclog release vX.Y.Z` to create a summary of all of the changes
      in this release.
   3. Committing the updated `CHANGELOG.md` file and `.changelog` directory to the repo.
2. Push this to a branch `release/vX.Y.Z` according to the version number of
   the anticipated release (e.g. `release/v0.17.0`) and open a **draft PR**.
3. Bump all relevant versions in the codebase to the new version and push these
   changes to the release PR. This includes:
   1. All `Cargo.toml` files (making sure dependencies' versions are updated
      too).
   2. All crates' `lib.rs` files documentation references' `html_root_url`
      parameters must point to the new version.
   3. Every reference to Hermes version in the [guide](./guide).

   **Important:** The `ibc-proto` crate version must only be bumped if it has
   changed since the last release. All other crates are bumped together.

4. Run `cargo doc --all-features --open` locally to double-check that all the
   documentation compiles and seems up-to-date and coherent. Fix any potential
   issues here and push them to the release PR.
5. Mark the PR as **Ready for Review** and incorporate feedback on the release.
6. Once approved, merge the PR.
7. Pull `master` and run the [`release.sh`](./scripts/release.sh) script.
   If any problem arises, submit a new PR, get it merged to `master` and try again.
   The reason for not releasing straight from the release branch, and therefore losing the
   ability to fix publishing problems as they arise, is that we would like the embedded
   metadata of the published crates, namely the Git commit at which the release was done,
   to match the Git commit on the `master` branch which will be tagged.
   [See this article][crates.io-security] for a more in-depth explanation.  
   **Note:** This step requires the appropriate privileges to push crates to [crates.io].
8. Once all crates have been successfully released, create a signed tag and push it to
   GitHub: `git tag -s -a vX.Y.Z`. In the tag message, write the version and the link
   to the corresponding section of the changelog.
9. Once the tag is pushed, wait for the CI bot to create a GitHub release, and update
   the release description to `[📖 CHANGELOG](https://github.com/informalsystems/ibc-rs/blob/master/CHANGELOG.md#vXYZ)`.
10. Wait an hour or so, and check that the CI job has uploaded the Hermes binaries to the release.
11. All done! 🎉

[crates.io]: https://crates.io
[crates.io-security]: https://codeandbitters.com/published-crate-analysis/
