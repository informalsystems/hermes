// ensure_no_std/src/main.rs
#![no_std]
#![allow(unused_imports)]

// Import the crates that we want to check if they are fully no-std compliance

#[cfg(feature = "use-ibc")]
use ibc;

#[cfg(feature = "use-ibc")]
use ibc_proto;

#[cfg(feature = "use-substrate")]
use sp_core;

#[cfg(feature = "use-substrate")]
use sp_io;

#[cfg(feature = "use-substrate")]
use sp_runtime;

#[cfg(feature = "use-substrate")]
use sp_std;

#[cfg(feature = "tonic")]
use tonic;

#[cfg(feature = "socket2")]
use socket2;

#[cfg(feature = "getrandom")]
use getrandom;

#[cfg(feature = "serde")]
use serde;

#[cfg(feature = "serde_json")]
use serde_json;

#[cfg(feature = "thiserror")]
use thiserror;

#[cfg(feature = "regex")]
use regex;

use flex_error;
use prost;
use prost_types;
use chrono;
use bytes;
use serde_derive;
use tracing;
use sha2;

use core::panic::PanicInfo;

/*

This function definition checks for the compliance of no-std in
dependencies by causing a compile error if  this crate is
linked with `std`. When that happens, you should see error messages
such as follows:

```
error[E0152]: found duplicate lang item `panic_impl`
  --> no-std-check/src/lib.rs
   |
12 | fn panic(_info: &PanicInfo) -> ! {
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: the lang item is first defined in crate `std` (which `offending-crate` depends on)
```

 */
#[cfg(not(feature = "use-substrate"))]
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}
