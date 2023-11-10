# ADR 007: Error Management

## Changelog

* 2020-07-26: Initial Proposal

## Context

This document describes the reason behind the switch from using
`anomaly` for error handling to
the [`flex-error`](https://docs.rs/flex-error/) crate that is developed in-house.

## Decision

### Problem Statement

To keep things brief, we will look at the issue of error handling from a specific example
in `relayer/src/error.rs`:

```rust
pub type Error = anomaly::Error<Kind>;

#[derive(thiserror::Error)]
pub enum Kind {
    #[error("GRPC error")]
    Grpc,
    ...
}

impl Kind {
    pub fn context(self, source: impl Into<Box<dyn std::error::Error>>) -> anomaly::Context<Self> {
        Context::new(self, Some(source.into()))
    }
}
```

The design above is meant to separate between two concerns:

  - The metadata about an error, as captured in `Kind`.
  - The trace of how the error occurred, as captured in `anomaly::Context`.
  - The type `Error` is defined to be `anomaly::Error<Kind>`, which is a newtype wrapper to `Box<anomaly::Context<Kind>>`.

There are a few issues with the original design using `anomaly`:

  - The error source type is erased and turned into a `Box<dyn std::error::Error>`, making it difficult to recover metadata
    information about the original error.
  - The `Kind::context` method allows any error type to be used as an error source, making it difficult to statically
    analyze which sub-error has what kind of error source.

We can demonstrate the design issue with a specific use case:

```rust
pub fn unbonding_period(&self) -> Result<Duration, Error> {
    let mut client = self
        .block_on(QueryClient::connect(self.grpc_addr.clone()))
        .map_err(|e| Kind::Grpc.context(e))?;

    let request = Request::new(QueryParamsRequest {});

    let response = self
        .block_on(client.params(request))
        .map_err(|e| Kind::Grpc.context(e))?;
    ...
}
```

Without the help of an IDE, it would be challenging to figure out that
the first use of `Kind::Grpc.context` has `tonic::Status` as the error source
type, while the second use has the error source type
`tonic::TransportError`.

The mixing up of `tonic::Status` and `tonic::TransportError` as error sources
are not too critical in this specific case. However this would not be the
case if we want to use the error source information to determine whether
an error is _recoverable_ or not. For instance, let's say if we want to
implement custom retry logic only when the error source is
`std::io::Error`, there is not easy way to distinguished if an error
variant `Kind::Grpc` is caused by `std::io::Error`.

### Proposed Design

A better design is to define error construction functions with _explicit_
error sources. The proposed design is as follows:

```rust
pub struct Error(pub ErrorDetail, pub eyre::Report);

pub enum ErrorDetail {
    GrpcStatus {
        status: tonic::Status
    },
    GrpcTransport,
    ...
}

impl Error {
    pub fn grpc_status(status: tonic::Status) -> Error {
        let detail = ErrorDetail::GrpcStatus { status };
        Error(detail, Eyre::msg(detail))
    }

    pub fn grpc_transport(source: tonic::TransportError) -> Error {
        let detail = ErrorDetail::GrpcTransport;
        let trace = Eyre::new(source).wrap_err(detail);
        Error(detail, trace)
    }
}
```

There are a few things addressed by the design above:
  - We use the `eyre::Report` type as an _error tracer_ to trace
    the error sources, together with additional information such as backtrace.
  - Depending on the error source type, we want to have different strategies
    to trace the error.
      - For example, we may not care about the metadata
        inside `tonic::TransportError`, so we just discard the data
        after tracing it using `eyre`.
  - We define _error constructor functions_ that handle the error source using
    different strategies. The function constructs the `ErrorDetail` and
    `eyre::Report` values, and then wrap them as the `Error` tuple.

In general, when the error sources are defined by external libraries,
we have little control of how the types are defined, and need to have
different ways to handle them.
But when we have multiple error types that are defined in the same crate,
we want to have special way to handle the propagation of error.

For example, consider the `LinkError` type, which has the error
we defined earlier as the error source:

```rust
use crate::error::{Error as RelayerError, ErrorDetail as RelayerErrorDetail};

pub struct LinkError(LinkErrorDetail, eyre::Report);

pub enum LinkErrorDetail {
    Relayer {
        source: RelayerErrorDetail
    },
    ...
}

impl LinkError {
    pub fn relayer_error((source_detail, trace): RelayerError) -> LinkError {
        let detail = LinkErrorDetail::Relayer(source_detail);
        LinkError(detail, trace.wrap_err(detail))
    }
}
```

We propagate the error detail to LinkErrorDetail so that we can recover
additional detail later on. Furthermore, we extract the `eyre::Report`
from the error source and use it to add additional information
when we construct `LinkError`.

### `flex-error`

The proposed design has a lot of boilerplate required to properly define
the error types. To reduce boilerplate, we have developed
[`flex-error`](https://docs.rs/flex-error/) with the `define_error!`
macro which makes it straightforward to implement the error types
using a DSL syntax. With that, the error types can instead be defined as:

```rust
use flex_error::{define_error, TraceError};

define_error! {
    Error {
        GrpcStatus
            { status: GrpcStatus }
            | e | { format!("GRPC call return error status {0}", e.status) },
        GrpcTransport
            [ TraceError<tonic::TransportError> ]
            | _ | { "error in underlying transport when making GRPC call" },
        ...
    }
}
```

Aside from the syntactic sugar provided by the `define_error!` macro, `flex-error`
also allows error tracer implementation to be switched based on the Cargo feature
flags set on the `flex-error` crate. For example, we can switch from the
[`eyre`](https://docs.rs/eyre/) tracer to the [`anyhow`](https://docs.rs/anyhow/)
tracer by disabling `"flex-error/eyre_tracer"` and enabling `"flex-error/anyhow_tracer"` features.

If all error tracer features and the `"flex-error/std"` feature are disabled,
a simple `flex_error::StringTracer` is used for tracing errors. The `StringTracer`
do not provide additional information such as back trace, but it is useful
for supporting `no_std`, where standard constructs such as `std::error::Error` and
error backtrace are not available.

The full documentation for `flex-error` is available at [Docs.rs](https://docs.rs/flex-error/).

## Status

Accepted - The PR has been merged in [#988](https://github.com/informalsystems/hermes/pull/988)

## Consequences

All error definitions in the `ibc-rs` project will be defined using the
`flex-error` crate.

### Positive

- Fine grained error handling.
- Flexible error tracing.
- `no_std` support.

### Negative

- It takes time to learn about the DSL and how to manage different error sources.
- Compile errors arise inside the macros may be difficult to debug.
- IDE provides limited integration for code inside macros.

### Neutral

- The error variants are defined in the `ErrorDetail::ErrorVariant{...}` convention,
  but the error constructor functions are defined in the `Error::error_variant(...)`
  convention.

## References

- [PR #988](https://github.com/informalsystems/hermes/pull/988):
  Use flex-error to define errors
- [Issue #712](https://github.com/informalsystems/hermes/issues/712):
  Relayer error handling specification
- [Issue #11588](https://github.com/informalsystems/hermes/issues/1158):
  Tracking issue for no-std support
