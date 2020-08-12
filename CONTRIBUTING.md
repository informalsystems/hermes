# Contributing

Thank you for your interest in contributing. The goal
of ibc-rs is to provide a high quality, formally verified implementation of
the IBC protocol.

All work on the code base should be motivated by a Github
Issue. Search is a good place start when looking for places to contribute. If you
would like to work on an issue which already exists, please indicate so
by leaving a comment. If you'd like to work on something else, open an Issue to
start the discussion.

The rest of this document outlines the best practices for contributing to this
repository:

- [Decision Making](#decision-making) - process for agreeing to changes
- [Forking](#forking) - fork the repo to make pull requests
- [Changelog](#changelog) - changes must be recorded in the changelog
- [Pull Requests](#pull-requests) - what makes a good pull request

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

TODO: ADR registration (eg. in an ADR registration issue)

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

![Contributing
flow](https://github.com/tendermint/tendermint/blob/v0.33.6/docs/imgs/contributing.png)

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

Every non-trivial PR must update the [CHANGELOG.md].

The Changelog is *not* a record of what Pull Requests were merged;
the commit history already shows that. The Changelog is a notice to the user
about how their expectations of the software should be modified. 
It is part of the UX of a release and is a *critical* user facing integration point.
The Changelog must be clean, inviting, and readable, with concise, meaningful entries. 
Entries must be semantically meaningful to users. If a change takes multiple
Pull Requests to complete, it should likely have only a single entry in the
Changelog describing the net effect to the user.

When writing Changelog entries, ensure they are targeting users of the software,
not fellow developers. Developers have much more context and care about more
things than users do. Changelogs are for users. 

Changelog structure is modeled after 
[Tendermint
Core](https://github.com/tendermint/tendermint/blob/master/CHANGELOG.md)
and 
[Hashicorp Consul](http://github.com/hashicorp/consul/tree/master/CHANGELOG.md).
See those changelogs for examples.

Changes for a given release should be split between the five sections: Security, Breaking
Changes, Features, Improvements, Bug Fixes.

Changelog entries should be formatted as follows:

```
- [pkg] \#xxx Some description about the change (@contributor)
```

Here, `pkg` is the part of the code that changed (typically a
top-level crate, but could be <crate>/<module>), `xxx` is the pull-request number, and `contributor`
is the author/s of the change.

It's also acceptable for `xxx` to refer to the relevent issue number, but pull-request
numbers are preferred.
Note this means pull-requests should be opened first so the changelog can then
be updated with the pull-request's number.

Changelog entries should be ordered alphabetically according to the
`pkg`, and numerically according to the pull-request number.

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
- update the [changelog](#changelog) with a description of the change

Pull requests should aim to be small and self contained to facilitate quick
review and merging. Larger change sets should be broken up across multiple PRs.
Commits should be concise but informative, and moderately clean. Commits will be squashed into a
single commit for the PR with all the commit messages.
