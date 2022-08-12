# Querier Consumer


```rust
# use std::fmt::Display;
# use std::convert::{TryFrom, TryInto};
#
# trait NamedPerson {
#      fn name(&self) -> &str;
# }
#
# trait HasError {
#      type Error;
# }
#
# trait PersonContext {
#      type PersonId;
#      type Person: NamedPerson;
# }
#
# trait Greeter<Context>
# where
#      Context: PersonContext + HasError,
# {
#      fn greet(&self, context: &Context, person_id: &Context::PersonId)
#          -> Result<(), Context::Error>;
# }
#
# trait KvStore: HasError {
#      fn get(&self, key: &str) -> Result<Vec<u8>, Self::Error>;
# }
#
# trait KvStoreContext {
#      type Store: KvStore;
#
#      fn store(&self) -> &Self::Store;
# }
#
# struct KvStorePersonQuerier;
#
# impl<Context, Store, PersonId, Person, Error, ParseError, StoreError>
#      PersonQuerier<Context> for KvStorePersonQuerier
# where
#      Context: KvStoreContext<Store=Store>,
#      Context: PersonContext<Person=Person, PersonId=PersonId>,
#      Context: HasError<Error=Error>,
#      Store: KvStore<Error=StoreError>,
#      PersonId: Display,
#      Person: TryFrom<Vec<u8>, Error=ParseError>,
#      Error: From<StoreError>,
#      Error: From<ParseError>,
# {
#      fn query_person(context: &Context, person_id: &PersonId)
#          -> Result<Person, Error>
#      {
#          let key = format!("persons/{}", person_id);
#
#          let bytes = context.store().get(&key)?;
#
#          let person = bytes.try_into()?;
#
#          Ok(person)
#      }
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
struct SimpleGreeter;

impl<Context> Greeter<Context> for SimpleGreeter
where
    Context: PersonContext + HasError,
    KvStorePersonQuerier: PersonQuerier<Context>,
{
    fn greet(&self, context: &Context, person_id: &Context::PersonId)
        -> Result<(), Context::Error>
    {
        let person = KvStorePersonQuerier::query_person(context, person_id)?;
        println!("Hello, {}", person.name());
        Ok(())
    }
}
```

## Generic Querier Consumer

Now that we have a context-generic implementation of `KvStorePersonQuerier`,
we can try to use it from `SimpleGreeter`. To do that, `SimpleGreeter` has
to somehow get `KvStorePersonQuerier` from `Context` and use it as a
`PersonQuerier`.

Recall that `KvStorePersonQuerier` itself is not a context (though it does
implement `PersonQuerier<Context>` in order to query a context), and therefore
it does not implement other context traits like `PersonContext`. What we
need instead is for concrete contexts like `AppContext` to specify that
their implementation of `PersonQuerier` is `KvStorePersonQuerier`.
We can do that by defining a `CanQueryPerson` trait as follows:

```rust
# trait NamedPerson {
#      fn name(&self) -> &str;
# }
#
# trait HasError {
#      type Error;
# }
#
# trait PersonContext {
#      type PersonId;
#      type Person: NamedPerson;
# }
#
# trait Greeter<Context>
# where
#      Context: PersonContext + HasError,
# {
#      fn greet(&self, context: &Context, person_id: &Context::PersonId)
#          -> Result<(), Context::Error>;
# }
#
trait PersonQuerier<Context>
where
    Context: PersonContext + HasError,
{
     fn query_person(context: &Context, person_id: &Context::PersonId)
         -> Result<Context::Person, Context::Error>;
}

trait CanQueryPerson:
    PersonContext + HasError + Sized
{
    type PersonQuerier: PersonQuerier<Self>;

    fn query_person(&self, person_id: &Self::PersonId)
        -> Result<Self::Person, Self::Error>
    {
        Self::PersonQuerier::query_person(self, person_id)
    }
}

struct SimpleGreeter;

impl<Context> Greeter<Context> for SimpleGreeter
where
    Context: CanQueryPerson,
{
    fn greet(&self, context: &Context, person_id: &Context::PersonId)
        -> Result<(), Context::Error>
    {
        let person = context.query_person(person_id)?;
        println!("Hello, {}", person.name());
        Ok(())
    }
}
```

While the `PersonQuerier` trait is implemented by component types like
`KvStorePersonQuerier`, the `CanQueryPerson` trait is implemented by
context types like `AppContext`. Compared to the earlier design of
`PersonQuerier`, the context is now offering a _component_ for
querying for a person that will work in the _current context_.

We can see that the `CanQueryPerson` trait has `PersonContext`
and `HasError` as its supertraits, indicating that the concrete context
also needs to implement these two traits first. Due to quirks in Rust,
the trait also requires the `Sized` supertrait, which is already implemented
by most types other than `dyn Trait` types, so that we can use `Self` inside
other generic parameters.

In the body of `CanQueryPerson`, we define a `PersonQuerier` associated
type, which implements the trait `PersonQuerier<Self>`. This looks a little
self-referential, as the context is providing a type that is referencing back
to itself. But with the dependency injection mechanism of the traits system,
this in fact works most of the time as long as there are no actual cyclic
dependencies.

Now inside the `Greet` implementation for `SimpleGreeter`, we require the
generic `Context` to implement `CanQueryPerson`. Inside the `greet`
method, we then call `Context::PersonQuerier::query_person` and pass in
the `context` as the first argument to query for the person details.

In summary, what we achieved at this point is as follows:

- We define a context-generic component for `PersonQuerier` as
    `KvStorePersonQuerier`.
- We define another context-generic component for `Greet` as `SimpleGreeter`,
    which _depends_ on a `PersonQuerier` component provided from the context.
- The Rust trait system _resolves_ the dependency graph, constructs a
    `KvStorePersonQuerier` using its _indirect dependencies_ from the context,
    and passes it as the `PersonQuerier` dependency to `SimpleGreeter`.

By using dependency injection, we don't need to know about the fact that in
order to build `SimpleGreeter`, we need to first build `KvStorePersonQuerier`,
but in order to build `KvStorePersonQuerier`, we need to first build
`FsKvStore`.

By leveraging dependency injection, we don't need to know that building
`SimpleGreeter` requires first building `KvStorePersonQuerier`, which itself
requires first building `FsKvStore`. The compiler resolves all of these
dependencies at compile time for free, and we do not even need to pay for the
cost of doing such wiring at run time.
