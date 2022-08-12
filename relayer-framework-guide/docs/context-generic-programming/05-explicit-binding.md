# Explicit Associated Type Binding

As we can see, by having generic type parameters as associated types in the
traits that `Context` implements, we are able to keep just one generic type
parameter in the `greet` function.

However, it is still possible for us to explicitly pull out `Error` as a generic
type parameter and bind to the `Error` associated type as follows:

```rust
# struct PersonId(String);
# struct Person {
#      id: PersonId,
#      name: String,
# }
#
# trait HasError {
#      type Error;
# }
#
# trait PersonQuerier: HasError {
#      fn query_person(&self, person_id: &PersonId) ->    Result<Person, Self::Error>;
# }
#
fn greet<Context, Error>(context: &Context, person_id: &PersonId)
    -> Result<(), Error>
where
    Context: PersonQuerier<Error=Error>,
{
    let person = context.query_person(person_id)?;
    println!("Hello, {}", person.name);
    Ok(())
}
```

By specifying the trait bound `Context: PersonQuerier<Error=Error>`,
we state that the `greet` function works with any generic type `Error`,
provided that `Context::Error` is the same as `Error`. With the explicit
binding, we are able to have `greet` return `Result<(), Error>` instead of
`Result<(), Context::Error>`.

There are sometimes benefits when we bind the associated types to an explicit
generic type parameter. For one, the inferred type shown in IDEs like
Rust Analyzer would be simpler, as they are shown as `Error` instead of
the fully qualified syntax `<Context as HasError>::Error`.
As we will see later, explicit type parameters also help us by providing a
way to specify the additional trait bounds of the associated types.

Aside from that, it is up to the programmer to decide whether to bind
the associated types to explicit type parameters. The key thing to understand
here is that the explicit bindings are optional, and we can choose to
omit such parameters whenever it is appropriate.
