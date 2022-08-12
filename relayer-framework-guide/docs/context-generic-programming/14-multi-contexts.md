# Multiple Context Implementations

We now look at the problem of having multiple context implementations,
as well as how to deduplicate them. For this we will focus on just the
implementation for `PersonQuerier` that is being used by `SimpleGreeter`.

The requirement for querying a person details can be implemented in many
ways, such as using a key-value store (KV store) or an SQL database.
Now suppose we have the following API for a KV store:

```rust
struct FsKvStore { /* ... */ }
struct KvStoreError { /* ... */ }

impl FsKvStore {
    fn get(&self, key: &str) -> Result<Vec<u8>, KvStoreError> {
        unimplemented!() // stub
    }
    // ...
}
```

We could implement `PersonQuerier` for any context type that
contains `FsKvStore` in its field:

```rust
# use std::convert::{TryFrom, TryInto};
#
# struct FsKvStore { /* ... */ }
# struct KvStoreError { /* ... */ }
#
# impl FsKvStore {
#      fn get(&self, key: &str) -> Result<Vec<u8>, KvStoreError> {
#          unimplemented!() // stub
#      }
#      // ...
# }
#
# trait HasError {
#      type Error;
# }
#
# trait PersonContext {
#      type PersonId;
#      type Person;
# }
#
# trait PersonQuerier: PersonContext + HasError {
#      fn query_person(&self, person_id: &Self::PersonId)
#          -> Result<Self::Person, Self::Error>;
# }
#
struct BasicPerson {
    name: String,
}

struct ParseError { /* ... */ }

impl TryFrom<Vec<u8>> for BasicPerson {
    type Error = ParseError;

    fn try_from(bytes: Vec<u8>) -> Result<Self, Self::Error> {
        unimplemented!() // stub
    }
}

struct AppContext {
    kv_store: FsKvStore,
    // ...
}

enum AppError {
    KvStore(KvStoreError),
    Parse(ParseError),
    // ...
}

impl HasError for AppContext {
    type Error = AppError;
}

impl PersonContext for AppContext {
    type PersonId = String;
    type Person = BasicPerson;
}

impl PersonQuerier for AppContext {
    fn query_person(&self, person_id: &Self::PersonId)
        -> Result<Self::Person, Self::Error>
    {
        let key = format!("persons/{}", person_id);
        let bytes = self.kv_store.get(&key)
            .map_err(AppError::KvStore)?;

        let person = bytes.try_into()
            .map_err(AppError::Parse)?;

        Ok(person)
    }
}
```

Even this simplified version of the implementation for `query_person` involves
quite a bit of logic. First, we need to implement serialization logic
to parse `BasicPerson` from raw bytes. We also need to implement the logic
of mapping the namespaced key from the person ID, as well as mapping
the errors in each operation into `AppError`s.

Fortunately, with the context traits design pattern, components like
`SimpleGreeter` do not need to be aware of how `PersonQuerier` is
implemented, or the existence of the key-value store in the context.
However, it would still be problematic if we need to re-implement
`PersonQuerier` for every new context type that we implement.

To avoid copying the body of `query_person` for all context types,
we want to have a _generic_ implementation of `PersonQuerier`
for _any_ context that has `FsKvStore` in one of its fields.
But if we recall from earlier sections, we already came up with
the design pattern for implementing context-generic components
like `Greeter`. So why not just turn `PersonQuerier` itself
into a context-generic component?

In fact, with a little re-arrangement, we can redefine
`PersonQuerier` as `PersonQuerier` as follows:

```rust
# trait HasError {
#      type Error;
# }
#
# trait PersonContext {
#      type PersonId;
#      type Person;
# }
#
trait PersonQuerier<Context>
where
    Context: PersonContext + HasError,
{
     fn query_person(context: &Context, person_id: &Context::PersonId)
         -> Result<Context::Person, Context::Error>;
}
```

We now have a `PersonQuerier` component that is parameterized by a generic
`Context` type, and it looks very similar to how we define `Greeter`.
With this, we can now define a context-generic implementation of
`PersonQuerier` for any context that has an `FsKvStore`:

```rust
# use std::fmt::Display;
# use std::convert::{TryFrom, TryInto};
#
# struct FsKvStore { /* ... */ }
# struct KvStoreError { /* ... */ }
#
# impl FsKvStore {
#      fn get(&self, key: &str) -> Result<Vec<u8>, KvStoreError> {
#          unimplemented!() // stub
#      }
#      // ...
# }
#
# trait HasError {
#      type Error;
# }
#
# trait PersonContext {
#      type PersonId;
#      type Person;
# }
#
# trait PersonQuerier<Context>
# where
#      Context: PersonContext + HasError,
# {
#         fn query_person(context: &Context, person_id: &Context::PersonId)
#             -> Result<Context::Person, Context::Error>;
# }
#
trait KvStoreContext {
    fn kv_store(&self) -> &FsKvStore;
}

struct KvStorePersonQuerier;

impl<Context, PersonId, Person, Error, ParseError>
    PersonQuerier<Context> for KvStorePersonQuerier
where
    Context: KvStoreContext,
    Context: PersonContext<Person=Person, PersonId=PersonId>,
    Context: HasError<Error=Error>,
    PersonId: Display,
    Person: TryFrom<Vec<u8>, Error=ParseError>,
    Error: From<KvStoreError>,
    Error: From<ParseError>,
{
    fn query_person(context: &Context, person_id: &PersonId)
        -> Result<Person, Error>
    {
        let key = format!("persons/{}", person_id);

        let bytes = context.kv_store().get(&key)?;

        let person = bytes.try_into()?;

        Ok(person)
    }
}
```

We first define a `KvStoreContext` trait, which allows us to extract
a reference to `FsKvStore` out of a context that implements it.
Following that, we define `KvStorePersonQuerier` as an empty struct,
similar to how we defined `SimpleGreeter`.

We then implement `PersonQuerier` for `KvStorePersonQuerier` to
work with any `Context` type, given that several additional constraints
are satisfied. We also use explicit type parameter bindings to simplify
the specification of our constraints.

We require `Context` to implement `KvStoreContext`, so that we can
extract `FsKvStore` from it. We also require `Context::PersonId` to
implement `Display` so that we can format the key as a string. Similarly,
we require that `Context::Person` implements `TryFrom<Vec<u8>>`
and bind the conversion error to an additional type binding `ParseError`.

The above bindings essentially make it possible for `KvStorePersonQuerier`
to work with not only any context that provides `FsKvStore`, but also
any `Context::PersonId` and `Context::Person` types as long as they
implement the `Display` and `TryFrom` traits.

We additionally require `Context::Error` to allow injection of sub-errors
from `KvStoreError` and `ParseError`, so that we can propagate the errors
inside `query_person`. If an error arises either when fetching bytes from the
store via the `context.kv_store().get()` call, or when parsing those bytes via
the `bytes.try_into()` call, the `?` operator will implicitly call `into()`
appropriately in order to coerce the error into an `Error`.
