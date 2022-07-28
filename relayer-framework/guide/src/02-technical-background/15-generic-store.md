# Generic Store

We managed to get `KvStorePersonQuerier` we defined earlier to not only
work with a generic context containing an `FsKvStore`, but also work
with any `PersonId` and `Person` types that satisfy some constraints.

We can further generalize the implementation of `KvStorePersonQuerier`
to work with _any_ key-value store implementation. With that, we will
for example be able to swap our store implementation from file-based
to in-memory easily.

```rust
# use core::fmt::Display;
#
# trait ErrorContext {
#   type Error;
# }
#
# trait PersonContext {
#   type PersonId;
#   type Person;
# }
#
# trait PersonQuerier<Context>
# where
#   Context: PersonContext + ErrorContext,
# {
#    fn query_person(context: &Context, person_id: &Context::PersonId)
#      -> Result<Context::Person, Context::Error>;
# }
#
trait KvStore: ErrorContext {
  fn get(&self, key: &str) -> Result<Vec<u8>, Self::Error>;
}

trait KvStoreContext {
  type Store: KvStore;

  fn store(&self) -> &Self::Store;
}

struct KvStorePersonQuerier;

impl<Context, Store, PersonId, Person, Error, ParseError, StoreError>
  PersonQuerier<Context> for KvStorePersonQuerier
where
  Context: KvStoreContext<Store=Store>,
  Context: PersonContext<Person=Person, PersonId=PersonId>,
  Context: ErrorContext<Error=Error>,
  Store: KvStore<Error=StoreError>,
  PersonId: Display,
  Person: TryFrom<Vec<u8>, Error=ParseError>,
  Error: From<StoreError>,
  Error: From<ParseError>,
{
  fn query_person(context: &Context, person_id: &PersonId)
    -> Result<Person, Error>
  {
    let key = format!("persons/{}", person_id);

    let bytes = context.store().get(&key)?;

    let person = bytes.try_into()?;

    Ok(person)
  }
}
```

We first define a `KvStore` trait that provides a `get` method for reading
values from the store. It also has `ErrorContext` as its supertrait, so
that we can reuse the `Error` associated type.

We then redefine the `KvStoreContext` to contain an associated type `Store`,
which is required to implement the `KvStore` trait. We then make the
`store` method return a reference to `Self::Store`.

Inside the `PersonQuerier` implementation for `KvStorePersonQuerier`, we
introduce two new explicit type bindings: `Store` for `Context::Store`,
and `StoreError` for `Store::Error`. We also require the main
`Error` type to implement `From<StoreError>`, so that any error from
the store can be propagated.
