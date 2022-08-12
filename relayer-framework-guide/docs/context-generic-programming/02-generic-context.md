# Generic Context

There are ways that we can make our `greet` function in Rust works more flexibly
similar to its dynamic-typed counterparty. First, we define a concrete `Context`
type as follows:

```rust
# struct PersonId(String);
# struct Person {
#      id: PersonId,
#      name: String,
# }
#
# struct Database { /* ... */}
# struct DbError { /* ... */}
# impl Database {
#      fn query_person(&self, person_id: &PersonId) -> Result<Person, DbError> {
#          unimplemented!() // stub
#      }
# }
#
struct Context {
    database: Database,
    // ...
}

fn greet(context: &Context, person_id: &PersonId) -> Result<(), DbError> {
    let person = context.database.query_person(person_id)?;
    println!("Hello, {}", person.name);
    Ok(())
}
```

At this stage, we have a concrete `Context` struct that contains the database
handle as well as other environment parameters that we may need. However,
`Context` is still concrete, so it is difficult to reuse the `greet` function
in a different context. So let's make the `Context` generic instead:

```rust
# struct PersonId(String);
#
# struct Person {
#      id: PersonId,
#      name: String,
# }
#
# struct Database { /* ... */}
# struct DbError { /* ... */}
#
# impl Database {
#      fn query_person(&self, person_id: &PersonId) -> Result<Person, DbError> {
#          unimplemented!() // stub
#      }
# }
#
trait ContextWithDatabase {
    fn database(&self) -> &Database;
}

fn greet<Context>(context: &Context, person_id: &PersonId) -> Result<(), DbError>
where
    Context: ContextWithDatabase,
{
    let person = context.database().query_person(person_id)?;
    println!("Hello, {}", person.name);
    Ok(())
}
```

In our first attempt, we turn `Context` into a generic type parameter.
With that, the concrete details of the context are lost, and we no longer
know how to access the fields such as the database. But we can recover that
by defining a `ContextWithDatabase` trait, which provides read-only
access to extract a reference to `Database` from the context.

With that, we are able to make `greet` work with any context type as
long as it contains a field for `Database`. For example:

```rust
# struct Database { /* ... */}
#
# trait ContextWithDatabase {
#      fn database(&self) -> &Database;
# }
#
struct AppContext {
    database: Database
}

impl ContextWithDatabase for AppContext {
    fn database(&self) -> &Database {
        &self.database
    }
}
```

However, since the `Database` type is concrete, it is challenging if we
want to run `greet` with an environment without a database, such as
an in-memory key-value store, cache store, or a blockchain. What we can do
instead is to define methods such that we can query for a person's details
directly from the context:


```rust
# struct PersonId(String);
# struct Person {
#      id: PersonId,
#      name: String,
# }
#
struct Error { /* ... */}

trait PersonQuerier {
    fn query_person(&self, person_id: &PersonId) -> Result<Person, Error>;
}

fn greet<Context>(context: &Context, person_id: &PersonId)
    -> Result<(), Error>
where
    Context: PersonQuerier,
{
    let person = context.query_person(person_id)?;
    println!("Hello, {}", person.name);
    Ok(())
}
```

We define a `PersonQuerier` trait that exposes a method for querying for a
person's details directly from the context. With that, we can have our `greet`
function work with any context type that knows how to query for person details,
regardless of whether it is implemented as a database query.
## Context with Error

One thing to note however is that the `Error` type in `PersonQuerier`
is concrete. With that, it would be problematic if we want to define new contexts
that have different query methods but also return different errors. While it
is possible to define a dynamic error type such as `Box<dyn Error>`, such type
erasure would mean that we lose information about what kinds of errors can happen
when we try to query for `Person` details.

We can instead make the error type _generic_. But instead of using it as a
generic parameter for `greet`, we can define it as an _associated type_ for
the generic type `Context`:

```rust
# struct PersonId(String);
# struct Person {
#      id: PersonId,
#      name: String,
# }
#
trait HasError {
    type Error;
}

trait PersonQuerier: HasError {
    fn query_person(&self, person_id: &PersonId) -> Result<Person, Self::Error>;
}

fn greet<Context>(context: &Context, person_id: &PersonId) -> Result<(), Context::Error>
where
    Context: PersonQuerier,
{
    let person = context.query_person(person_id)?;
    println!("Hello, {}", person.name);
    Ok(())
}
```

We define a new `HasError` trait with only one thing, which is the `Error`
associated type. Aside from that, there is nothing known about the `Error`
type, but that is ok as we will see later on. The trait `PersonQuerier`
then has `HasError` as its supertrait, esentially allowing it to access
the associated type as `Self::Error` in the return type of `query_person`.

We define the `Error` associated type in a separate `HasError` trait,
instead of directly in the `PersonQuerier` trait. As we will see later,
this is essential to allow multiple context traits to access the same
`Error` type.

In the `greet` function, we require the generic `Context` type to
implement `PersonQuerier`. But since `HasError` is a supertrait of
`PersonQuerier`, we would also able to access the error type as
`Context::Error`.

## Explicit Associated Type Binding

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

## Generic Person

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

trait HasError {
    type Error;
}

trait PersonContext {
    type PersonId;
    type Person: NamedPerson;
}

trait PersonQuerier: PersonContext + HasError {
    fn query_person(
        &self,
        person_id: &Self::PersonId,
    ) -> Result<Self::Person, Self::Error>;
}

fn greet<Context>(
    context: &Context,
    person_id: &Context::PersonId,
) -> Result<(), Context::Error>
where
    Context: PersonQuerier,
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

The `PersonQuerier` is now defined with `PersonContext` as another of its
supertraits. With that, the `query_person` method becomes completely abstract.
A generic consumer would only know that, given an abstract type
`Context::PersonId`, it can query the `Context` and either get back an abstract
type `Context::Person` that implements `NamedPerson`, or get back an abstract
error `Context::Error`.
