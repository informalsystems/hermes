extern crate alloc as _alloc;
extern crate std as _std;

#[cfg(feature = "std")]
pub use _std::string::{String, ToString};

#[cfg(not(feature = "std"))]
pub use _alloc::string::{String, ToString};

#[cfg(feature = "std")]
pub use _std::format;

#[cfg(not(feature = "std"))]
pub use _alloc::format;

#[cfg(feature = "std")]
pub use std::error::Error as StdError;

use crate::events::Error as EventError;
use crate::ics02_client::height::Error as HeightError;
use crate::ics24_host::error::ValidationError;
use crate::timestamp::ParseTimestampError;
use core::convert::Infallible;
use core::fmt::{Debug, Display};
use core::num::ParseIntError;

#[cfg(not(feature = "std"))]
pub trait StdError: Debug + Display {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        None
    }
}

#[derive(Debug)]
pub struct DummyError(String);

impl Display for DummyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "DummyError: {}", self.0)
    }
}

impl From<String> for DummyError {
    fn from(value: String) -> DummyError {
        DummyError(value)
    }
}

impl From<&str> for DummyError {
    fn from(value: &str) -> DummyError {
        DummyError(value.into())
    }
}

impl From<Infallible> for DummyError {
    fn from(_value: Infallible) -> DummyError {
        DummyError("Infallible".into())
    }
}

impl From<ParseIntError> for DummyError {
    fn from(_value: ParseIntError) -> DummyError {
        DummyError("ParseIntError".into())
    }
}

impl From<ValidationError> for DummyError {
    fn from(_value: ValidationError) -> DummyError {
        DummyError("ValidationError".into())
    }
}

impl From<EventError> for DummyError {
    fn from(_value: EventError) -> DummyError {
        DummyError("EventError".into())
    }
}

impl From<HeightError> for DummyError {
    fn from(_value: HeightError) -> DummyError {
        DummyError("HeightError".into())
    }
}

impl From<ParseTimestampError> for DummyError {
    fn from(_value: ParseTimestampError) -> DummyError {
        DummyError("ParseTimestampError".into())
    }
}

impl StdError for DummyError {}
