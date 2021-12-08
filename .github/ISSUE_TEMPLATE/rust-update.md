---
name: Rust version update
about: A checklist to perform to update to a new version of Rust.
---

# Update to Rust release 1.x.y

🦀

- [ ] Update the version in `rust-toolchain.toml`.
- [ ] Run `cargo clippy --all-features --fix`, review and commit the automatic
      fixes, and fix all reported lints. Try to resolve the root causes for
      the lints rather than silencing them with `#[allow(...)]`.

## Update the MSRV (optional)

Additional steps to perform in order to make the new minimal supported
Rust version:

- [ ] Update the `rust-version` fields in all `Cargo.toml` files.
- [ ] Update the `msrv` field in `clippy.toml` and fix all lints reported by
      `cargo clippy --all-features`.
- [ ] Update the MSRV shields in README files:
  - `README.md`
  - `relayer-rest/README.md`
- [ ] Update the MSRV in the guide: `guide/src/pre_requisites.md`
- [ ] Add a `.changelog` entry to the `breaking-changes` section,
      announcing the new MSRV.
