//! In-house alternative to [`unwrap-infallible`].
//!
//! Enables the following pattern in our codebase:
//!
//! ```
//! use std::convert::TryInto;
//! use ibc_proto::ibc::core::client::v1::Height as ProtoHeight;
//! use ibc::Height;
//! use ibc::utils::UnwrapInfallible;
//!
//! let ph = ProtoHeight { revision_height: 1, revision_number: 54 };
//! let h: Height = ph
//!         .try_into()             // returns a `Result<Height, Infallible>`
//!         .unwrap_infallible();   // converts safely into `Height`
//! ```
//!
//! [`unwrap-infallible`]: [https://crates.io/crates/unwrap-infallible

use std::convert::Infallible;

// TODO: Remove this trait and its associated impl once `into_ok` stabilizes:
//  https://github.com/rust-lang/rust/issues/61695
pub trait UnwrapInfallible {
    type Output;

    fn unwrap_infallible(self) -> Self::Output;
}

impl<A> UnwrapInfallible for Result<A, Infallible> {
    type Output = A;

    fn unwrap_infallible(self) -> Self::Output {
        match self {
            Ok(a) => a,
            Err(_) => unreachable!(),
        }
    }
}

#[test]
fn test() {
    let x: Result<i32, Infallible> = Ok(42);
    assert_eq!(x.unwrap_infallible(), 42);
}
