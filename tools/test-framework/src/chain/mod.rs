/*!
   Constructs for spawning and managing full nodes, e.g. the
   Gaia chains.

   Note that this is different from the "chains" being referred on
   the relayer side in [`ibc_relayer`]. In testing we also need
   to refer to the actual chains running rather than the chain client that
   communicate with the chain.

   There is not yet good terminology to differentiate the two sides.
   For now we will refer to the running chains as full nodes or
   chain servers when qualification is needed, while keeping the original
   chain terminology in the relayer unchanged to avoid having to
   rename existing constructs in the relayer code.
*/

pub mod builder;
pub mod chain_type;
pub mod config;
pub mod driver;
pub mod exec;
pub mod tagged;
pub mod version;
