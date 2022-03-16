/*!
   Framework code for making it easier to write test cases.

   If you want to create a common test setup that is shared
   by multiple test cases, the best way is to define them as
   new traits within the [`framework`](crate::framework) module.

   The actual operations for bootstrapping the test setup
   should *not* be implemented in this module. Instead, they
   should be implemented as functions in the
   [`bootstrap`](crate::bootstrap) module. This is so that
   test writers can still have the option to manually
   bootstrap the test setup without getting locked-in to
   using the test framework.

   We can think of the test framework as being a DSL for
   making it easier to write _declarative_ tests. On the
   other hand, the [`bootstrap`](crate::bootstrap) module
   allows the same test setup to be done in an _imperative_ way.

   ## Common Test Cases

   Here is a short list of common traits that are used for
   defining simple test scenarios:

   - [`BinaryNodeTest`](binary::node::BinaryNodeTest) -
     Test with two full nodes running without setting up the relayer.
   - [`BinaryChainTest`](binary::chain::BinaryChainTest) -
     Test with two full nodes running with the relayer setup with chain handles.
   - [`BinaryChannelTest`](binary::channel::BinaryChannelTest) -
     Test with two full nodes running with the relayer setup with chain handles
     together with channels that are already connected.
*/

pub mod base;
pub mod binary;
pub mod nary;
pub mod overrides;
