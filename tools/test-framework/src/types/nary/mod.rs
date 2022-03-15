/*!
  Definitions for tagged data structures involving N-ary chains.

  In the binary version of the tagged data structures, we use the
  existential types `ChainA: ChainHandle` and `ChainB: ChainHandle`
  to differentiate between two chains. Since Rust treat each type
  differently, we can use `ChainA` and `ChainB` as type tags
  to differentiate values coming from different chains.
  For example, `DualTagged<ChainA, ChainB, ChannelId>`
  can be used to refer to a `ChainId` on `ChainA` with the
  counterparty chain being `ChainB`.

  When extending to the N-ary case, we can no longer use
  existential types to refer to each chain, because we cannot
  know before hand how many types are needed. Instead,
  we can use _const generics_ to identify chains by _position_.

  The first construct we need is the [`Size`](aliases::Size) struct,
  which lifts a const generic `usize` into a type:

  ```rust
  enum Size<const TAG: usize> {}
  ```

  Using `Size`, we can for example use a `usize` as a tag.
  For example, `MonoTagged<Size<42>, String>` is a `String`
  that is tagged by the `usize` value `42`.

  Aside from the position, we still need to be able to differentiate
  values coming from different _collections_ of chains. For example,
  given a first collection `[ChainA, ChainB, ChainC]`, and a second
  collection `[ChainD, ChainE]`, a naively position-tagged value like
  `MonoTagged<Size<1>, Denom>` could be used to refer to a denomination
  that come from either `ChainB` or `ChainE`, which defeats the purpose
  of tagging values with type tags.

  Due to the initial design of using the `ChainHandle` existential type as
  the type tag, it is also required that any type that is used to tag
  values for chains to also implement `ChainHandle`. Since `Size` does
  not implement `ChainHandle`, it is also not possible to use it directly
  as tags in structures such as `ForeignClient`.

  Instead, we also require an existential `Collection: ChainHandle` type
  to identify all chains within an N-ary collection. We then tag
  the handle with the position, before tagging it again with the
  values. For example, a `Denom` that is tagged with the third chain
  in the first collection would be written as
  `MonoTagged<MonoTagged<Size<2>, Collection1>, Denom>`.
  The tagging also works because we have defined a `ChainHandle`
  implementation for `MonoTagged<Tag, Chain>` for any `Chain: ChainHandle`.

  The current approach for tagging N-ary chain values is a bit cumbersome.
  To save the effort of typing the fully qualified type of N-ary tagged
  values, we also define type aliases such as
  [`NthChainHandle`](aliases::NthChainHandle) and
  [`NthForeignClient`](foreign_client::NthForeignClient).
  This would still result in overly verbose messages in type errors involving
  these types. If necessary, we will refactor these defintions as newtypes
  so that they can be used and shown in a cleaner form.
*/

pub mod aliases;
pub mod chains;
pub mod channel;
pub mod connection;
pub mod foreign_client;
