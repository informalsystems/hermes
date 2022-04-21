# Architecture Decision Records (ADR)

This is a location to record all high-level architecture decisions in the IBC-RS project.

You can read more about the ADR concept in this [blog post](https://product.reverb.com/documenting-architecture-decisions-the-reverb-way-a3563bb24bd0#.78xhdix6t).

An ADR should provide:

- Context on the relevant goals and the current state
- Proposed changes to achieve the goals
- Summary of pros and cons
- References
- Changelog

Note the distinction between an ADR and a spec. The ADR provides the context, intuition, reasoning, and
justification for a change in architecture, or for the architecture of something
new. The spec is much more compressed and streamlined summary of everything as
it is or should be.

If recorded decisions turned out to be lacking, convene a discussion, record the new decisions here, and then modify the code to match.

Note the context/background should be written in the present tense.

To suggest an ADR, please make use of the [ADR template](./adr-template.md) provided.

## Table of Contents

| ADR \#                                           | Description                       | Status |
|--------------------------------------------------|-----------------------------------| ------ |
| [001](./adr-001-repo.md)                         | Repository structure for `ibc-rs` | Accepted    |
| [002](./adr-002-ibc-relayer.md)                  | IBC Relayer in Rust               | Accepted |
| [003](./adr-003-handler-implementation.md)       | IBC handlers implementation       | Accepted |
| [004](./adr-004-relayer-domain-decomposition.md) | Relayer domain decomposition      | Accepted |
| [005](./adr-005-relayer-v0-implementation.md)    | Relayer v0 implementation         | Accepted |
| [006](./adr-006-hermes-v0.2-usecases.md)         | Hermes v0.2.0 Use-Cases           | Proposed |
| [007](./adr-007-ics20-implementation.md)         | ICS20 implementation              | Proposed |
