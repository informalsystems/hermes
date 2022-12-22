---
name: New Release Request
about: Create a proposal to track the release of a new version of Hermes
---

<!-- < < < < < < < < < < < < < < < < < < < < < < < < < < < < < < < < < ☺ 
v               ✰  Thanks for opening a release issue! ✰
v    Before smashing the submit button please review the template.
v    Word of caution: poorly thought-out proposals may be rejected 
v                     without deliberation 
☺ > > > > > > > > > > > > > > > > > > > > > > > > > > > > > > > > >  -->


# Release Hermes v.X.Y.Z 

⚡

- [ ] Bump all crate versions to the new version
- [ ] Update `Cargo.lock`
- [ ] Create a new release in the changelog, using [`unclog`](https://github.com/informalsystems/unclog)
  - If doing a release candidate (`rc`) version, then skip the `unclog release` step
- [ ] Reassign unfinished issues of previous milestone to the next milestone
