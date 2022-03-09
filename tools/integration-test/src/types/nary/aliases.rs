use crate::types::tagged::*;

/**
   Lifts a const generic `usize` into a type.

   This allows us to use `usize` as a tag, for example,
   `MonoTagged<Size<1>, String>` is a `String` that is
   tagged by the const generic `1`.
*/
pub enum Size<const TAG: usize> {}

/**
   Tag a `Handle: ChainHandle` type with a const generic `TAG: usize`.

   In an N-ary chain implementation, we have to use the same
   [`Handle: ChainHandle`](ibc_relayer::chain::handle::ChainHandle)
   type for all elements in the N-ary data structures. However since the
   [`ChainHandle`](ibc_relayer::chain::handle::ChainHandle) type is
   also being used to tag other values, we want to be able to differentiate
   between tagged values coming from chains at different positions
   in the N-ary setup.

   The solution is to tag each `Handle` with the const generic
   positions. With that a position-tagged type like
   `MonoTagged<Size<0>, Handle>` would have a different type
   from the type tagged at a different position like
   `MonoTagged<Size<1>, Handle>`.

   To reduce the boilerplate, we define the type alias
   `TaggedHandle` so that less typing is needed to refer
   to `ChainHandle`s that are tagged by position.

*/
pub type NthChainHandle<const POS: usize, Handle> = MonoTagged<Size<POS>, Handle>;
