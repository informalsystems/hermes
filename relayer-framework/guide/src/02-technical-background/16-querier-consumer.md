# Querier Consumer

Now that we have a context-generic implementation of `KvStorePersonQuerier`,
we can try to use it from `SimpleGreeter`. To do that, `SimpleGreeter` has
to somehow get `KvStorePersonQuerier` from `Context`, and use it as a
`PersonQuerier`.

Recall that `KvStorePersonQuerier` itself is not a context, and therefore
it does not implement other context traits like `PersonContext`. What we
need instead is for concrete contexts like `AppContext` to specify that
their implementation of `PersonQuerier` is `KvStorePersonQuerier`.
We can do that by defining a `PersonQuerierContext` trait as follows:

```rust
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
trait PersonQuerier<Context>
where
  Context: PersonContext + ErrorContext,
{
   fn query_person(context: &Context, person_id: &Context::PersonId)
     -> Result<Context::Person, Context::Error>;
}

trait PersonQuerierContext:
  PersonContext + ErrorContext + Sized
{
  type PersonQuerier: PersonQuerier<Self>;
}

struct SimpleGreeter;

impl<Context> Greeter<Context> for SimpleGreeter
where
  Context: PersonQuerierContext,
{
  fn greet(&self, context: &Context, person_id: &Context::PersonId)
    -> Result<(), Context::Error>
  {
    let person = Context::PersonQuerier::query_person(context, person_id)?;
    println!("Hello, {}", person.name());
    Ok(())
  }
}
```

While the `PersonQuerier` is implemented by component types like
`KvStorePersonQuerier`, the `PersonQuerierContext` trait is implemented by
context types like `AppContext`. Compared to the earlier design of
`QueryPersonContext`, the context is now offering a _component_ for
querying person that also works in the _current context_.

We can see that the `PersonQuerierContext` trait has `PersonContext`
and `ErrorContext` as its supertraits, indicating that the concrete context
also needs to implement the other two traits first. Due to quirks in Rust,
the trait also requires the `Sized` supertrait, which is already implemented
by most types other than `dyn Trait` types, so that we can use `Self` inside
other generic parameters.

In the body of `PersonQuerierContext`, we define a `PersonQuerier` associated
type, which implements the trait `PersonQuerier<Self>`. This looks a little
self-referential, as the context is providing a type that is referencing back
to itself. But with the dependency injection mechanism of the traits system,
this in fact works most of the time as long as there is no actual cyclic
dependencies.

Now inside the `Greet` implementation for `SimpleGreeter`, we require the
generic `Context` to implement `PersonQuerierContext`. Inside the `greet`
method, we then call `Context::PersonQuerier::query_person` and pass in
the `context` as first argument to query for the person details.

In summary, what we achieved at this point is as follows:

- We define a context-generic component for `PersonQuerier` as
  `KvStorePersonQuerier`.
- We define another context-generic component for `Greet` as `SimpleGreeter`,
  which _depends_ on a `PersonQuerier` component provided from the context.
- The Rust trait system _resolves_ the dependency graph, constructs
  `KvStorePersonQuerier` from its _indirect dependencies_ from the context,
  and "pass" it as the `PersonQuerier` dependency to `SimpleGreeter`.

By using dependency injection, we don't need to know that in order to build
`SimpleGreeter`, we need to first build `KvStorePersonQuerier`, but in order
to build `KvStorePersonQuerier`, we need to first build `FsKvStore`. During
compile-time, Rust does all the wiring for free, and we do not even need to
pay for the cost of doing such wiring at run time.
