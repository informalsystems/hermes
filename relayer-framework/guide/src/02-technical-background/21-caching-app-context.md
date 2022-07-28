# Caching App Context

```rust
# use core::hash::Hash;
# use core::fmt::Display;
# use std::collections::HashMap;
#
# trait NamedPerson {
#   fn name(&self) -> &str;
# }
#
# trait ErrorContext {
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
#   Context: PersonContext + ErrorContext,
# {
#   fn greet(&self, context: &Context, person_id: &Context::PersonId)
#     -> Result<(), Context::Error>;
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
# trait KvStore: ErrorContext {
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
#   Context: ErrorContext<Error=Error>,
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
#   PersonContext + ErrorContext + Sized
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
#[derive(Clone)]
struct BasicPerson {
  name: String,
}

# impl NamedPerson for BasicPerson {
#   fn name(&self) -> &str {
#     &self.name
#   }
# }
#
# trait PersonCacheContext: PersonContext {
#   fn person_cache(&self) -> &HashMap<Self::PersonId, Self::Person>;
# }
#
# struct CachingPersonQuerier<InQuerier>(InQuerier);
#
# impl<Context, InQuerier> PersonQuerier<Context>
#   for CachingPersonQuerier<InQuerier>
# where
#   InQuerier: PersonQuerier<Context>,
#   Context: PersonCacheContext,
#   Context: ErrorContext,
#   Context::PersonId: Hash + Eq,
#   Context::Person: Clone,
# {
#   fn query_person(context: &Context, person_id: &Context::PersonId)
#     -> Result<Context::Person, Context::Error>
#   {
#     let entry = context.person_cache().get(person_id);
#
#     match entry {
#       Some(person) => Ok(person.clone()),
#       None => InQuerier::query_person(context, person_id),
#     }
#   }
# }
#
# struct FsKvStore { /* ... */ }
# struct KvStoreError { /* ... */ }
#
# struct ParseError { /* ... */ }
#
# impl ErrorContext for FsKvStore {
#   type Error = KvStoreError;
# }
#
# impl KvStore for FsKvStore {
#   fn get(&self, key: &str) -> Result<Vec<u8>, Self::Error> {
#     unimplemented!() // stub
#   }
# }
#
# impl TryFrom<Vec<u8>> for BasicPerson {
#   type Error = ParseError;
#
#   fn try_from(bytes: Vec<u8>) -> Result<Self, Self::Error> {
#     unimplemented!() // stub
#   }
# }
#
# enum AppError {
#   KvStore(KvStoreError),
#   Parse(ParseError),
#   // ...
# }
#
# impl From<KvStoreError> for AppError {
#   fn from(err: KvStoreError) -> Self {
#     Self::KvStore(err)
#   }
# }
#
# impl From<ParseError> for AppError {
#   fn from(err: ParseError) -> Self {
#     Self::Parse(err)
#   }
# }
#
struct AppContext {
  kv_store: FsKvStore,
  person_cache: HashMap<String, BasicPerson>,
  // ...
}

# impl ErrorContext for AppContext {
#   type Error = AppError;
# }
#
# impl PersonContext for AppContext {
#   type PersonId = String;
#   type Person = BasicPerson;
# }
#
# impl KvStoreContext for AppContext {
#   type Store = FsKvStore;
#
#   fn store(&self) -> &Self::Store {
#     &self.kv_store
#   }
# }
#
impl PersonCacheContext for AppContext {
  fn person_cache(&self) -> &HashMap<String, BasicPerson> {
    &self.person_cache
  }
}

impl PersonQuerierContext for AppContext {
  type PersonQuerier = CachingPersonQuerier<KvStorePersonQuerier>;
}

fn app_greeter() -> impl Greeter<AppContext> {
  SimpleGreeter
}
```
