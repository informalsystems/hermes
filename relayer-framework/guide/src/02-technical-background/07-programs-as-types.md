# Programs as Types

The `greet` function that we have defined at this point can now work with
any context type that implements the required traits. In practice, we may
also want to implement different versions of the `greet` function so that
they can be consumed generically by other components.

With the generic context design, we define a `Greeter` interface that
is parameterized by a generic context, and can be used by any other
components that also share the same context. This can be defined as
follows:

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
# trait QueryPersonContext: PersonContext + ErrorContext {
#   fn query_person(&self, person_id: &Self::PersonId)
#     -> Result<Self::Person, Self::Error>;
# }
#
trait Greeter<Context>
where
  Context: PersonContext + ErrorContext,
{
  fn greet(&self, context: &Context, person_id: &Context::PersonId)
    -> Result<(), Context::Error>;
}

struct SimpleGreeter;

impl<Context> Greeter<Context> for SimpleGreeter
where
  Context: QueryPersonContext,
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

The `Greeter` trait is defined to be parameterized by a generic `Context` type,
which is required to implement both `PersonContext` and `ErrorContext`.
The `greet` method is then defined without generic parameters, as these have been
captured in the trait definition. We then define an empty struct `SimpleGreeter`,
which is there only to implement the `Greeter` trait for any `Context` type
that implements `QueryPersonContext`.

It is worth noticing here that in the main `Greeter` trait definition,
the `Context` type, is only required to implement `PersonContext` and
`ErrorContext`, but there is no mention of the `QueryPersonContext`
trait bound. On the other hand, the concrete `Greeter` implementation
for `SimpleGreeter` can require the additional trait bound
`Context: QueryPersonContext` in its `impl` definition.

This demonstrates the benefits of separating the `QueryPersonContext`
from the `PersonContext` trait: From the perspective of a consumer
that uses the `Greeter` component, it does not need to know whether
the generic context type implements `QueryPersonContext`. This means
that from the trait bounds alone, we can tell whether a piece of code
can call `query_person` directly, or whether it can only call the
`greet` method to greet a person without knowing how the greeter determined
the person's name.
