# Store Context Implementation

```rust
# use std::fmt::Display;
# use std::convert::{TryFrom, TryInto};
#
# trait NamedPerson {
#   fn name(&self) -> &str;
# }
#
# trait HasError {
#   type Error;
# }
#
# trait PersonContext {
#   type PersonId;
#   type Person: NamedPerson;
# }
#
# trait Greeter<Context>
# where
#   Context: PersonContext + HasError,
# {
#   fn greet(&self, context: &Context, person_id: &Context::PersonId)
#     -> Result<(), Context::Error>;
# }
#
# trait PersonQuerier<Context>
# where
#   Context: PersonContext + HasError,
# {
#    fn query_person(context: &Context, person_id: &Context::PersonId)
#      -> Result<Context::Person, Context::Error>;
# }
#
# trait KvStore: HasError {
#   fn get(&self, key: &str) -> Result<Vec<u8>, Self::Error>;
# }
#
# trait KvStoreContext {
#   type Store: KvStore;
#
#   fn store(&self) -> &Self::Store;
# }
#
# struct KvStorePersonQuerier;
#
# impl<Context, Store, PersonId, Person, Error, ParseError, StoreError>
#   PersonQuerier<Context> for KvStorePersonQuerier
# where
#   Context: KvStoreContext<Store=Store>,
#   Context: PersonContext<Person=Person, PersonId=PersonId>,
#   Context: HasError<Error=Error>,
#   Store: KvStore<Error=StoreError>,
#   PersonId: Display,
#   Person: TryFrom<Vec<u8>, Error=ParseError>,
#   Error: From<StoreError>,
#   Error: From<ParseError>,
# {
#   fn query_person(context: &Context, person_id: &PersonId)
#     -> Result<Person, Error>
#   {
#     let key = format!("persons/{}", person_id);
#
#     let bytes = context.store().get(&key)?;
#
#     let person = bytes.try_into()?;
#
#     Ok(person)
#   }
# }
#
# trait PersonQuerierContext:
#   PersonContext + HasError + Sized
# {
#   type PersonQuerier: PersonQuerier<Self>;
# }
#
# struct SimpleGreeter;
#
# impl<Context> Greeter<Context> for SimpleGreeter
# where
#   Context: PersonQuerierContext,
# {
#   fn greet(&self, context: &Context, person_id: &Context::PersonId)
#     -> Result<(), Context::Error>
#   {
#     let person = Context::PersonQuerier::query_person(context, person_id)?;
#     println!("Hello, {}", person.name());
#     Ok(())
#   }
# }
#
# struct BasicPerson {
#   name: String,
# }
#
# impl NamedPerson for BasicPerson {
#   fn name(&self) -> &str {
#     &self.name
#   }
# }
#
struct FsKvStore { /* ... */ }
struct KvStoreError { /* ... */ }

struct ParseError { /* ... */ }

impl HasError for FsKvStore {
  type Error = KvStoreError;
}

impl KvStore for FsKvStore {
  fn get(&self, key: &str) -> Result<Vec<u8>, Self::Error> {
    unimplemented!() // stub
  }
}

impl TryFrom<Vec<u8>> for BasicPerson {
  type Error = ParseError;

  fn try_from(bytes: Vec<u8>) -> Result<Self, Self::Error> {
    unimplemented!() // stub
  }
}

enum AppError {
  KvStore(KvStoreError),
  Parse(ParseError),
  // ...
}

impl From<KvStoreError> for AppError {
  fn from(err: KvStoreError) -> Self {
    Self::KvStore(err)
  }
}

impl From<ParseError> for AppError {
  fn from(err: ParseError) -> Self {
    Self::Parse(err)
  }
}

struct AppContext {
  kv_store: FsKvStore,
  // ...
}

impl HasError for AppContext {
  type Error = AppError;
}

impl PersonContext for AppContext {
  type PersonId = String;
  type Person = BasicPerson;
}

impl KvStoreContext for AppContext {
  type Store = FsKvStore;

  fn store(&self) -> &Self::Store {
    &self.kv_store
  }
}

impl PersonQuerierContext for AppContext {
  type PersonQuerier = KvStorePersonQuerier;
}

fn app_greeter() -> impl Greeter<AppContext> {
  SimpleGreeter
}
```
