/*!
   A small library for adding one or two type tags to data types.

   This module introduces two data types, [`MonoTagged`] and
   [`DualTagged`], for adding one or two type tags to any data
   type, respectively.

   The main idea is that we add any type as a tag to a type,
   so that two values with different tags are considered
   different types.

   ```rust,compile_fail
   # use ibc_test_framework::types::tagged::*;
   struct Foo;
   struct Bar;

   // Helper to test whether two values have the same type.
   fn same<T>(_: T, _: T) {}

   let val1: i64 = 42; // A raw `i64` value.

   // An `i64` value tagged with the `Foo` type.
   let val2: MonoTagged<Foo, i64> = MonoTagged::new(42);

   // An `i64` value tagged with the `Bar` type.
   let val3: MonoTagged<Bar, i64> = MonoTagged::new(42);

   // error, because the tags `Foo` and `Bar` are different.
   same(val2, val3);
   ```

   The `tagged` library does not enforce how the type tags should be used
   correctly. Therefore we can freely add or remove tags for a value at
   any time. It is up to the user of this library to ensure that values
   are tagged with the proper type tag as intended.

   For example, it is entirely fine to do something like:

   ```rust
   # use ibc_test_framework::types::tagged::*;
   struct Foo;
   struct Bar;
   struct Baz;

   let val1: i64 = 42;

   // Add a new tag `Foo` to `val1`.
   let val2: MonoTagged<Foo, i64> = MonoTagged::new(val1);

   // Remove the tag `Foo` from `val2`.
   let val3: i64 = val2.into_value();

   // Retag `val3` with a new tag `Bar`.
   let val4: MonoTagged<Bar, i64> = MonoTagged::new(val3);

   // Directly retag `val4` from `Bar` tag to `Baz` tag.
   let val5: MonoTagged<Baz, i64> = val4.retag();
   ```

   As a result, user is free to switch to work with the untagged version
   of the values, if they find the tagged values to have too complicated
   types to deal with. The retagging approach also works well for
   interoperability between functions that use tagged and untagged values,
   so that there is no need to convert an entire code base to use
   tagged values.

   Currently the main use of the `tagged` library is to tag data types and
   identifiers associated with different chains. For example, a tagged
   type `DualTagged<ChainA, ChainB, ChannelId>` is used to represent
   a `ChannelId` value that is used on `ChainA` to identify a channel
   that is connected to `ChainB`. With the tagged identifier, it is
   more unlikely for us to accidentally use the `ChannelId` coming from
   counterparty chain, as it would have the the type
   `DualTagged<ChainB, ChainA, ChannelId>` and thus result in
   type error.

   Currently the type tags for the chain data types are derived from
   the spawned chain handles, which has the existential type
   [`impl ChainHandle`](ibc_relayer::chain::handle::ChainHandle).
   Note that even though there is only one implementation of
   `ChainHandle`,
   [`CountingAndCachingChainHandle`](ibc_relayer::chain::handle::CountingAndCachingChainHandle),
   when they are returned as `impl ChainHandle` they would be
   considered by Rust as an
   [abstract type](https://doc.rust-lang.org/reference/types/impl-trait.html#abstract-return-types)
   that is different from the original type. Inside generic functions,
   we can also treat the same type as different types by specifying
   them as separate generic parameters.

   By using `impl ChainHandle` as the type tag, it also encourage
   us to treat different `ChainHandle` values as having different
   types. This will help us in the future to have easier transition
   into implementing relayer code that support relaying between different
   implementations of `ChainHandle`s that corresponding to different
   chain implementations.


   The use of tagged identifiers are especially useful for avoiding confusion
   when using data types that have tags in _contravariant_ ordering,
   such as
   [`ForeignClient`](ibc_relayer::foreign_client::ForeignClient).
   Whereas most relayer constructs such as
   `Connection<ChainA, ChainB>`  would mean
   "a connection from chain A to chain B", a
   `ForeignClient<ChainA, ChainB>` actually means "a foreign client from
   chain B to chain A". As a result, if we want to always refer to
   "from chain A to chain B", then we would have to instead write
   `ForeignClient<ChainB, ChainA>`.

   The use of contravariant ordering can be very confusing for developers
   who are new to the code base, and we cannot expect developers to always
   remember which construct requires contravariant ordering. We also cannot
   easily refactor legacy constructs such as `ForeignClient` to use covariant
   ordering, as we would have to search for the entire code base to
   replace the ordering, and there is no guarantee to do the refactoring
   correctly.

   With tagged identifiers, we can alleviate some of the confusion by
   leaving it to the type system to track which identifier belong to
   which chain. This way if a developer ever think that
   `ForeignClient<ChainA, ChainB>` means "foreign client from chain A
   to chain B", the compiler will correct them of the mistake with a
   type error.
*/

pub mod dual;
pub mod mono;

pub use dual::Tagged as DualTagged;
pub use mono::Tagged as MonoTagged;
