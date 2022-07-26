# Technical Background

This section covers the technical background for understanding the programming
techniques used by the relayer framework. Readers with background in
dynamic-typed programming languages such as JavaScript and Python may find
the techniques used here to be similar to dynamic typed programming,
but with static type guarantees.

We will start with simple examples and then slowly relate them to the design
of the relayer framework.

## Simple Greeter

Let's say we want to write a simple greeter program that greets a person.
The simplest way is to write a function like follows:

```rust
fn greet(name: String) {
  println!("Hello, {}!", name);
}
```

When calling the greet function from a larger context, we may want to pass
a `Person` struct with a `name` attribute on it, so that the caller do not
have to know how to get the person's name.

```rust
struct Person {
  name: String,
  address: String,
  // ...
}

fn greet(person: &Person) {
  println!("Hello, {}!", person.name);
}
```

But the caller of the greet function might not have the person's information
on hand, as it may be stored in a database. So we might want to implement
a greet function that accepts a `PersonId` and a database handler, so that
it can load the person's information from the database, and then greets them.

```rust
struct PersonId(String);
struct Person {
  id: PersonId,
  name: String,
  address: String,
  // ...
}

struct Database { /* ... */}
struct DbError { /* ... */}
impl Database {
  fn query_person(&self, person_id: &PersonId) -> Result<Person, DbError> {
    unimplemented!() // stub
  }
}

fn greet(db: &Database, person_id: &PersonId) -> Result<(), DbError> {
  let person = db.query_person(person_id)?;
  println!("Hello, {}", person.name);
  Ok(())
}
```

As the application grows, we can see that the complexity creeps in pretty
quickly even with such simple example:

- The full details of the `Person` struct must be fetched regardless of
  whether the greet function needs it.
- The concrete implementation of `Database` is exposed to the gree function,
  making it difficult to work with other databases.
- The concrete error `DbError` from the database query is leaked into the
  greet function implementation.

When the application is still in its early stage, it might be tempting to
leave these concerns aside, and not worry about them too much. But eventually
we will reach a point where we need our application to work with different
implementations. For example:

- We may want a caching layer to cache the person's information instead of
  querying directly from database all the time.
- We may want to have different database implementations, such as mock
  database or in-memory database.
- We may want to have multiple concrete person types, so that the database
  only fetches the essentiall information. e.g. `PersonWithName`,
  `PersonWithFullDetails`, `PersonWithRoles` etc.

## Comparison with Dynamic Typing

One thing worth noting with our greet example in Rust is that many of the
problems are applicable because we are programming in a static typed
language. If we were to re-implement the greet function in a dynamic
typed language like JavaScript, many of the problems will go away:

```javascript
function greet(db, person_id) {
  let person = db.query_person(person_id)
  console.log(`Hello, ${person.name}!`)
}
```

Thanks to dynamic typing, the JavaScript `greet` function above is general
in many ways:

- The function can work with any `db` value, as long as they provide a valid
  `query_person` method.
- The function can work with any `person` value returned from `db.query_person`,
  as long as it contains a `name` field that can be serialized into string.
- The error can be thrown implicitly by `db.query_person` as an exception.

On the upside, the dynamic nature of the `greet` function means that it can be
easily reused across multiple database and person implementations. On the
downside, since there is no type information, it is easy to accidentally call
`greet` with invalid implementations and only discover the errors late during
runtime execution.

Ideally, we would like to have the same benefits of writing generalized programs
in dynamic types, but still enjoy the benefits of type checking when there are
mismatch in the specialized implementation.

## Dynamic Context

The first thing to notice when writing generalized functions is that there are
usually contextual values of the surrounding environment that is needed for
the program to execute successfully.

In our dynamic greet example, we can generalize the `db` value and think of it
as a `context` value, which may contain other environment parameters such as
configuration for the greet word used.

```javascript
function greet(context, person_id) {
  let person = context.query_person(person_id)
  console.log(`Hello, ${person.name}!`)
}
```

In the OOP world, the `context` value is typically referred to as a `self`
value. However for clarity and more structured composition, it is better
to think of it as a fully abstract value with unknown type. This would
allow the context value to be augmented in a functional way, without
having to resort to using any OOP class hierarchy.

## Static Context

Now getting back to Rust, we can first redefine our `greet` function in Rust
to use a concrete `Context` type:

```rust
# struct PersonId(String);
# struct Person {
#   id: PersonId,
#   name: String,
# }
#
# struct Database { /* ... */}
# struct DbError { /* ... */}
# impl Database {
#   fn query_person(&self, person_id: &PersonId) -> Result<Person, DbError> {
#     unimplemented!() // stub
#   }
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

## Generic Context

At this stage, we have a concrete `Context` struct that contains the database
handle as well as other environment parameters that we may need. However since
the context is concrete, it is still difficult to reuse the greet function
in a slightly different context. So let's make the context generic instead:

```rust
# struct PersonId(String);
# struct Person {
#   id: PersonId,
#   name: String,
# }
#
# struct Database { /* ... */}
# struct DbError { /* ... */}
# impl Database {
#   fn query_person(&self, person_id: &PersonId) -> Result<Person, DbError> {
#     unimplemented!() // stub
#   }
# }
#
trait ContextWithDatabase {
  fn database(&self) -> &Database;
}

fn greet<Context>(context: &Context, person_id: &PersonId)
  -> Result<(), DbError>
where
  Context: ContextWithDatabase,
{
  let person = context.database().query_person(person_id)?;
  println!("Hello, {}", person.name);
  Ok(())
}
```

In our first attempt, we turn `Context` into a generic type parameter.
With that, the concrete detail of the context is lost, and we no longer
know how to access the fields such as database. But we can recover that
by defining a `ContextWithDatabase` trait, which provides read only
access to extract a reference to `Database` from the context.

With that, we are able to make `greet` work with any context type as
long as it contains a field for `Database`. For example:

```rust
# struct Database { /* ... */}
# trait ContextWithDatabase {
#   fn database(&self) -> &Database;
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

However since the `Database` type is concrete, it is challenging if we
want to run `greet` with an environment without database, such as
an in-memory key-value store, cache store, or a blockchain. What we can do
instead is to define methods such that we can query for a person's details
directly from the context:


```rust
# struct PersonId(String);
# struct Person {
#   id: PersonId,
#   name: String,
# }
#
struct Error { /* ... */}
trait QueryPersonContext {
  fn query_person(&self, person_id: &PersonId) ->  Result<Person, Error>;
}

fn greet<Context>(context: &Context, person_id: &PersonId)
  -> Result<(), Error>
where
  Context: QueryPersonContext,
{
  let person = context.query_person(person_id)?;
  println!("Hello, {}", person.name);
  Ok(())
}
```

We define a `QueryPersonContext` trait that exposes method for querying for a
person's details directly from the context. With that, we can have our `greet`
function work with any context type that knows how to query for person details,
regardless of whether it is implemented as a database query.

## Error Context

One thing to note however is that the `Error` type in `QueryPersonContext`
is concrete. With that it would be problematic if we want to define new contexts
that have different query methods but also returns different errors. While it
is possible to define a dynamic error type such as `Box<dyn Error>`, such type
erasure would mean that we lost information about what kind of error can happen
when we try to query for a person detail.

We can instead make the error type _generic_. But instead of putting it as a
generic parameter for `greet`, we can define it as an _associated type_ for
the generic type `Context`:

```rust
# struct PersonId(String);
# struct Person {
#   id: PersonId,
#   name: String,
# }
#
trait ErrorContext {
  type Error;
}

trait QueryPersonContext: ErrorContext {
  fn query_person(&self, person_id: &PersonId) ->  Result<Person, Self::Error>;
}

fn greet<Context>(context: &Context, person_id: &PersonId)
  -> Result<(), Context::Error>
where
  Context: QueryPersonContext,
{
  let person = context.query_person(person_id)?;
  println!("Hello, {}", person.name);
  Ok(())
}
```

We define a new `ErrorContext` trait with only one thing, which is the `Error`
associated type. Aside from that, there is nothing known about the `Error`
type, but that is ok as we will see later on. The trait `QueryPersonContext`
then has `ErrorContext` as its supertrait, esentially allowing it to access
the associated type as `Self::Error` in the return type of `query_person`.

We define the `Error` associated type in a separate `ErrorContext` trait,
instead of directly in the `QueryPersonContext` trait. As we will see later,
this is essential to allow multiple context traits to access the same
`Error` type.

In the `greet` function, we keep on requiring the generic `Context` type to
implement `QueryPersonContext`. But since `ErrorContext` is a supertrait of
`QueryPersonContext`, we would also able to access the type as
`Context::Error`.

## Explicit Associated Type Binding

As we can see, by having generic type parameters as associated types in the
traits that `Context` implements, we are able to keep just one generic type
parameter in the `greet` function.

However it is still possible for us to explicitly pull out `Error` as a generic
type parameter, and then binding it to the `Error` associated type as follows:

```rust
# struct PersonId(String);
# struct Person {
#   id: PersonId,
#   name: String,
# }
#
# trait ErrorContext {
#   type Error;
# }
#
# trait QueryPersonContext: ErrorContext {
#   fn query_person(&self, person_id: &PersonId) ->  Result<Person, Self::Error>;
# }
#
fn greet<Context, Error>(context: &Context, person_id: &PersonId)
  -> Result<(), Error>
where
  Context: QueryPersonContext<Error=Error>,
{
  let person = context.query_person(person_id)?;
  println!("Hello, {}", person.name);
  Ok(())
}
```

By specifying the trait bound `Context: QueryPersonContext<Error=Error>`,
we state that the `greet` function works with any generic type `Error`,
provided that `Context::Error` is the same as `Error`. With the explicit
binding, we are able to have `greet` return `Result<(), Error>` instead of
`Result<(), Context::Error>`.

There are sometimes benefits when we bind the associated types to an explicit
generic type parameter. For one, the inferred type shown in IDEs like
Rust Analyzer would be simpler, as they are shown as `Error` instead of
the fully qualified syntax `<Context as ErrorContext>::Error`.
As we will see later, explicit type parameters also help us have a shorter
way to specify the additional trait bounds of the associated types.

Aside from that, it is up to the programmer to decide whether to bind
the associated types to explicit type parameters. The key to understand
here is that the explicit bindings are optional, and we can choose to
omit such parameters whenever it is appropriate.

## Generic Person

Right now our `Error` type has become generic, but our `Person` type is
still concrete. We may also want to make the `Person` type generic in
similar way, so that the `greet` function can work with any other
person types.

This may be essential for reasons such as performance. For instance,
depending on where `greet` is called, it may be desirable to load
all details about a person from the database so that it can be
cached, or minimal details to save bandwidth.

From the perspective of `greet`, it does not matter what fields a `Person`
type has, as long as it can extract the name of the person as string.
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
abstract, as we don't care whether it is a string, an integer, or a UUID.
The associated type `Person` is also abstract, but we also add a trait bound
that the type must implement `NamedPerson`.

The `QueryPersonContext` is now defined with `PersonContext` as another of its
supertrait. With that, the `query_person` method becomes completely abstract.
A generic consumer would only know that given an abstract type
`Context::PersonId`, it can query from the context and either get back an abstract
type `Context::Person` that implements `NamedPerson`, or get back an abstract
error `Context::Error`.

## Programs as Types

The `greet` function that we have defined at this point can now work with
any context type that implements the required traits. In practice, we may
also want to implement different versions of the greet function so that
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
  fn greet(context: &Context, person_id: &Context::PersonId)
    -> Result<(), Context::Error>;
}

struct SimpleGreeter;

impl<Context> Greeter<Context> for SimpleGreeter
where
  Context: QueryPersonContext,
{
  fn greet(context: &Context, person_id: &Context::PersonId)
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
The `greet` method is then defined without generic parameter, as it has been
captured in the trait parameter. We then define an empty struct `SimpleGreeter`,
which is there only to implement the `Greeter` trait for any `Context` type
that implements `QueryPersonContext`.

It is worth noticing here that in the main `Greeter` trait definition,
the `Context` type is only required to implement `PersonContext` and
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
`greet` method to greet a person without knowing how the greeter find out
the person's name.

## Context Implementation

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
# trait Greeter<Context>
# where
#   Context: PersonContext + ErrorContext,
# {
#   fn greet(context: &Context, person_id: &Context::PersonId)
#     -> Result<(), Context::Error>;
# }
#
# struct SimpleGreeter;
#
# impl<Context> Greeter<Context> for SimpleGreeter
# where
#   Context: QueryPersonContext,
# {
#   fn greet(context: &Context, person_id: &Context::PersonId)
#     -> Result<(), Context::Error>
#   {
#     let person = context.query_person(person_id)?;
#     println!("Hello, {}", person.name());
#     Ok(())
#   }
# }
// Database stubs
struct Database;
struct DbError;

struct BasicPerson {
  name: String,
}

enum AppError {
  Database(DbError),
  // ...
}

struct AppContext {
  database: Database,
}

impl ErrorContext for AppContext {
  type Error = AppError;
}

impl PersonContext for AppContext {
  type PersonId = String;
  type Person = BasicPerson;
}

impl NamedPerson for BasicPerson {
  fn name(&self) -> &str {
    &self.name
  }
}

impl QueryPersonContext for AppContext {
  fn query_person(&self, person_id: &Self::PersonId)
    -> Result<Self::Person, Self::Error>
  {
    unimplemented!() // database stub
  }
}

fn app_greeter() -> impl Greeter<AppContext> {
  SimpleGreeter
}
```
