# Generic Person

Right now, our `Error` type has become generic, but our `Person` type is
still concrete. We may also want to make the `Person` type generic in a
similar way, so that the `greet` function can work with any other
person types.

This may be essential for reasons such as performance. For instance,
depending on where `greet` is called, it may be desirable to load
all details about a person from the database so that it can be
cached, or conversely, it might be desirable to load minimal details in order to
save bandwidth.

From the perspective of `greet`, it does not matter what fields a `Person`
type has, as long as it can extract the name of the person as a string.
So we can generalize the `Person` type as follows:

```rust
trait NamedPerson {
  fn name(&self) -> &str;
}

trait ErrorContext {
  type Error;
}

trait PersonContext {
  type PersonId;
  type Person: NamedPerson;
}

trait QueryPersonContext: PersonContext + ErrorContext {
  fn query_person(&self, person_id: &Self::PersonId)
    -> Result<Self::Person, Self::Error>;
}

fn greet<Context>(context: &Context, person_id: &Context::PersonId)
  -> Result<(), Context::Error>
where
  Context: QueryPersonContext,
{
  let person = context.query_person(person_id)?;
  println!("Hello, {}", person.name());
  Ok(())
}
```

We first define a `NamedPerson` trait, with a `name` method to extract a string
out from the person. We also define a `PersonContext` trait that has two
associated types: `PersonId` and `Person`. The `PersonId` type is completely
generic, as we don't care whether it is a string, an integer, or a UUID.
The associated type `Person` is also generic, but we also add a trait bound
that the type must implement `NamedPerson`.

The `QueryPersonContext` is now defined with `PersonContext` as another of its
supertraits. With that, the `query_person` method becomes completely abstract.
A generic consumer would only know that, given an abstract type
`Context::PersonId`, it can query the `Context` and either get back an abstract
type `Context::Person` that implements `NamedPerson`, or get back an abstract
error `Context::Error`.
