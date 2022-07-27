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
- The concrete implementation of `Database` is exposed to the greet function,
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
  only fetches the essential information. e.g. `PersonWithName`,
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
  as long as it contains a `name` field that can be converted into string.
- The error can be thrown implicitly by `db.query_person` as an exception.

On the upside, the dynamic nature of the `greet` function means that it can
easily be reused across multiple database and person implementations. On the
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
#
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

In the `greet` function, we require the generic `Context` type to
implement `QueryPersonContext`. But since `ErrorContext` is a supertrait of
`QueryPersonContext`, we would also able to access the error type as
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
cached, or with minimal details to save bandwidth.

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

With the basic traits implemented, we now look at how we can define a
concrete context that satisfies the traits:

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
#   fn greet(&self, context: &Context, person_id: &Context::PersonId)
#     -> Result<(), Context::Error>;
# }
#
# struct SimpleGreeter;
#
# impl<Context> Greeter<Context> for SimpleGreeter
# where
#   Context: QueryPersonContext,
# {
#   fn greet(&self, context: &Context, person_id: &Context::PersonId)
#     -> Result<(), Context::Error>
#   {
#     let person = context.query_person(person_id)?;
#     println!("Hello, {}", person.name());
#     Ok(())
#   }
# }
struct BasicPerson {
  name: String,
}

impl NamedPerson for BasicPerson {
  fn name(&self) -> &str {
    &self.name
  }
}

struct AppContext {
  database: Database,
}

// Database stubs
struct Database;
struct DbError;

enum AppError {
  Database(DbError),
  // ...
}

impl ErrorContext for AppContext {
  type Error = AppError;
}

impl PersonContext for AppContext {
  type PersonId = String;
  type Person = BasicPerson;
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

We first define a `BasicPerson` struct with only a `name` field,
since that is the minimal information required for `greet` to work.
We implement `NamedPerson` for `BasicPerson`, by simply returning
`&self.name`.

We also define an `AppContext` struct, with a stub database field.
For demo purpose, we have a dummy `Database` struct, and a `DbError`
type to represent database errors. We also define an `AppError`
enum to represent all application errors, with one of them being
`DbError`.

We implement `ErrorContext` for `AppContext`, with `AppError` as
the `Error` type. We also implement `PersonContext` for `AppContext`,
with the `PersonId` associated type being `String`, and the `Person`
associated type being `BasicPerson`. We also implement `QueryPersonContext`,
but leave the `query_person` as a stub for performing database query
in an actual application.

Finally, we implement an `app_greeter` function as a _witness_ that
we can construct a type that implements `Greeter<AppContext>`.
The function is implemented by simply returning `SimpleGreeter`.
The fact that the function compiles provide evidence that
`SimpleGreeter` can _always_ be used as a `Greeter<AppContext>`.

## Compile-Time Dependency Injection

The `app_greeter` function above demonstrates a form of _dependency injection_
done at compile time. This is because for any code to use a type implementing
`Greeter<Context>`, they only need to know that `Context` implements
`ErrorContext` and `PersonContext`. But to make `SimpleGreeter` implement
`Greeter<Context>`, it also needs `Context` to implement `QueryPersonContext`.

When we return `SimpleGreeter` inside `app_greeter`, the Rust compiler would
figure out that `SimpleGreeter` requires `AppContext` to implement
`QueryPersonContext`. It would then try to automatically _resolve_ the
dependency by searching for an implementation of `QueryPersonContext`
for `AppContext`. Upon finding the implementation, Rust "binds" that
implementation with `SimpleGreeter`, and return it as an existential
type that implements `Greeter<AppContext>`. As a result,
We can treat the type returned from `app_greeter` as an abstract type,
and "forget" the fact that `AppContext` implements `QueryPersonContext`.

This pattern of making use of Rust's trait system for depedency injection
efficiently solves the
[context and capabilities problem](https://tmandry.gitlab.io/blog/posts/2021-12-21-context-capabilities/)
in Rust. Without it, we would have to rely on more exotic language features
that are not available in Rust, or resort to manual passing of dependencies
by hands.

For example, we could perform manual binding for an implementation similar
to `SimpleGreeter` as a purely generic function as follows:

```rust
# trait NamedPerson {
#   fn name(&self) -> &str;
# }
#
fn make_simpler_greeter<Context, PersonId, Person, Error>(
  query_person: impl Fn(&Context, &PersonId) -> Result<Person, Error>,
) -> impl Fn(&Context, &PersonId) -> Result<(), Error>
where
  Person: NamedPerson,
{
  move | context, person_id | {
    let person = query_person(context, person_id)?;
    println!("Hello, {}", person.name());
    Ok(())
  }
}
```

As we can see, the ad hoc function `make_simpler_greeter` that we defined is
much more verbose than the earlier trait-based implementation. We would
have to explicitly track 4 generic type parameters, and we would have to
manually pass in dependencies like `query_person` and return nested closures.

When we delegate the management of the context dependencies to Rust's trait
system, we can think of Rust making automatic binding of depedencies similar
to what's being done in the code above. The binding is not only automated,
but also much more efficient. Because the binding is done at compile time,
it allows Rust to perform any further optimization such as inlining the code.

As we will see later, the same resolution can be applied to _nested_
dependencies. Thanks to how the trait system works, we can specify
complex dependencies for our components, and have Rust figure out
how to stitch together the dependencies and construct the combined
components that we need.

## Component Composition

Now suppose that we want to extend our greeter component such that it only
greets a person at day time during office hours. We could directly modify
the `Greeter` implementation for `SimpleGreeter` to do that, but that may
complicate the implementation and makes it more difficult to understand
the core logic. Alternatively, we could define a new `DaytimeGreeter`
component that _wraps_ around the original `SimpleGreeter`.

In this new `DaytimeGreeter` component, it would need to know how to
get the current time of the system, as well as how to tell whether
a given time value is at daytime. Following the context pattern we
learned, we will also define a `TimeContext` trait for getting the time.

The full implementation is as follows:

```rust
# use core::time::Duration;
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
trait SimpleTime {
  fn is_daytime(&self) -> bool;
}

trait TimeContext {
  type Time;

  fn now(&self) -> Self::Time;
}

trait Greeter<Context>
where
  Context: PersonContext + ErrorContext,
{
  fn greet(&self, context: &Context, person_id: &Context::PersonId)
    -> Result<(), Context::Error>;
}

struct DaytimeGreeter<InGreeter>(InGreeter);

impl<Context, InGreeter> Greeter<Context> for DaytimeGreeter<InGreeter>
where
  InGreeter: Greeter<Context>,
  Context: TimeContext + PersonContext + ErrorContext,
  Context::Time: SimpleTime,
{
  fn greet(&self, context: &Context, person_id: &Context::PersonId)
    -> Result<(), Context::Error>
  {
    let now = context.now();
    if now.is_daytime() {
      self.0.greet(context, person_id)?;
    } else {
      println!("Sorry, the shop has closed now!");
    }
    Ok(())
  }
}
```

For demo purpose, we first define a `SimpleTime` trait that provides an
`is_daytime` method to tell whether the a time value is in daytime.
Following that, we define a `TimeContext` trait that provides a `now` method
to fetch the current time from the context. Notice that the associated type
`Time` does _not_ implement `SimpleTime`. This is so that we can learn how
to inject the `SimpleTime` constraint as an _indirect dependency_ using the
same dependency injection technique.

We then define the `DaytimeGreeter` with a `InGreeter` type parameter, which
would act as the inner `Greeter` component. We then define a generic
implementation of `Greeter<Context>` for `DaytimeGreeter<InGreeter>`.
In the trait bounds, we require the inner greeter `InGreeter` to also
implement `Greeter<Context>`, since the core logic is implemented over there.

Aside from `PersonContext` and `ErrorContext`, we also requires `Context`
to implement `TimeContext` for `DaytimeGreeter` to fetch the current time.
Other than that, we also explicitly requires that the associated type
`Context::Time` to implement `SimpleTime`.

By specifying `SimpleTime` as an explicit dependency, we relax the requirement
of how the `TimeContext` trait can be used by other components. So if
`SimpleTime` is only ever used by `DaytimeGreeter`, and if an application
do not need `DaytimeGreeter`, then a concrete context can skip implementing
`SimpleTime` for its time type, even if the trait `TimeContext` is used by
other components.

## Error Injection

In our earlier implementation of `DaytimeGreeter`, the greeter simply prints
out that the shop has closed, and then return successfully without calling
the inner greeter. But what if we want `DaytimeGreeter` to return an error
during night time? Since the associated type `Error` in `ErrorContext`
is abstract, there is no obvious way we can construct an error value of
type `Error`.

On the other hand, we learned in the earlier section that we can specify
additional trait bound for `Context::Time` to implement `SimpleTime`.
Similarly, we can also specify additional trait bounds for `Context::Error`
so that we gain additional knowledge on how to construct an error value.

We can do this by defining a custom `ShopClosedError` struct, and require
`Context::Error` to implement a `From` instance for conversion from
`ShopClosedError`:

```rust
# use core::time::Duration;
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
# trait SimpleTime {
#   fn is_daytime(&self) -> bool;
#
#   fn duration_since(&self, other: &Self) -> Duration;
# }
#
# trait TimeContext {
#   type Time;
#
#   fn now(&self) -> Self::Time;
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
struct ShopClosedError<Time> { time: Time }

struct DaytimeGreeter<InGreeter>(InGreeter);

impl<Context, InGreeter> Greeter<Context> for DaytimeGreeter<InGreeter>
where
  InGreeter: Greeter<Context>,
  Context: TimeContext + PersonContext + ErrorContext,
  Context::Time: SimpleTime,
  Context::Error: From<ShopClosedError<Context::Time>>,
{
  fn greet(&self, context: &Context, person_id: &Context::PersonId)
    -> Result<(), Context::Error>
  {
    let now = context.now();
    if now.is_daytime() {
      self.0.greet(context, person_id)
    } else {
      Err(ShopClosedError { time: now }.into())
    }
  }
}
```

The `ShopClosedError` is parameterized by a generic `Time` type, so that
it can provide detail about the time that caused `ShopClosedError` to be
raised. In the `Greeter` implementation for `DaytimeGreeter`, we add an
addition trait bound to require `Context::Error` to implement
`From<ShopClosedError<Context::Time>>`. With that, if the time returned
by `context.now()` is in night time, we can construct a `ShopClosedError`
and turn it into `Context::Error` using the `into` method.

What we have done above is essentially specifying an _error injection method_
for injecting a sub-error type into the main error type. With this, individual
components do not need to know about the concrete application error and all
the possible errors that can be raised. But they can still _inject_ specific
error into the main error type by requiring additional `From` constraints.

For instance, `DaytimeGreeter` do not need to be aware of whether the inner
greeter component would raise a database error. And from the `impl` definition,
we can be confident that `DaytimeGreeter` itself cannot raise any sub-error
other than `ShopClosedError`.

## Explicit Associated Type Bindings

When specifying the constraints for indirect depedencies, we have to keep using
the `Context::` prefix to access associated types like `Context::Error`. Worse,
once we start using nested associated types, we would have to resort to use
fully qualified syntaxes like `<Context::Foo as Foo>::Bar` instead of
`Context::Foo::Bar`.

To help simplify the trait bounds for components like `DaytimeGreeter`, we
can use the explicit associated type bindings we learn earlier:

```rust
# use core::time::Duration;
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
# trait SimpleTime {
#   fn is_daytime(&self) -> bool;
#
#   fn duration_since(&self, other: &Self) -> Duration;
# }
#
# trait TimeContext {
#   type Time;
#
#   fn now(&self) -> Self::Time;
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
# struct ShopClosedError<Time> { time: Time }
#
# struct DaytimeGreeter<InGreeter>(InGreeter);
#
impl<Context, InGreeter, Time, Error, PersonId>
  Greeter<Context> for DaytimeGreeter<InGreeter>
where
  InGreeter: Greeter<Context>,
  Context: ErrorContext<Error=Error>,
  Context: PersonContext<PersonId=PersonId>,
  Context: TimeContext<Time=Time>,
  Time: SimpleTime,
  Error: From<ShopClosedError<Time>>,
{
  fn greet(&self, context: &Context, person_id: &PersonId)
    -> Result<(), Error>
  {
    let now = context.now();
    if now.is_daytime() {
      self.0.greet(context, person_id)
    } else {
      Err(ShopClosedError { time: now }.into())
    }
  }
}
```

In our new `Greeter` implementation, we introduce the generic parameters
`Time`, `Error`, and `PersonId`. We then bind the types to the associated
types of the context traits, such as `ErrorContext<Error=Error>`. With the
bindings in place we can have simpler trait bounds like `Time: SimpleTime`
to be specified in place of the more verbose `Context::Time: SimpleTime`.

## Concrete Composition

Now that we have both `SimpleGreeter` and `DaytimeGreeter` implemented, we
can look at how we can define a fully application context that satisfies the
constraints of both greeters. To better structure our application, we also
separate out different parts of the code into separate modules.

First, we put all the abstract traits into a `traits` module:

```rust
mod app {
  mod traits {
    pub trait NamedPerson {
      fn name(&self) -> &str;
    }

    pub trait SimpleTime {
      fn is_daytime(&self) -> bool;
    }

    pub trait ErrorContext {
      type Error;
    }

    pub trait PersonContext {
      type PersonId;
      type Person: NamedPerson;
    }

    pub trait TimeContext {
      type Time;

      fn now(&self) -> Self::Time;
    }
  }

  // ...
}
```

This module do not contain any concrete type definition, and thus can have
minimal dependency to external crates.

In practice, the trait definitions can be placed in different sub-modules, so
that we can have more fine grained control of which traits a component depends
on.

Next, we define `SimpleGreeter` and `DaytimeGreeter` in separate modules.

```rust
mod app {
  mod traits {
    // ...
#    pub trait NamedPerson {
#      fn name(&self) -> &str;
#    }
#
#    pub trait SimpleTime {
#      fn is_daytime(&self) -> bool;
#    }
#
#    pub trait ErrorContext {
#      type Error;
#    }
#
#    pub trait PersonContext {
#      type PersonId;
#      type Person: NamedPerson;
#    }
#
#    pub trait TimeContext {
#      type Time;
#
#      fn now(&self) -> Self::Time;
#    }
#
#    pub trait QueryPersonContext: PersonContext + ErrorContext {
#      fn query_person(&self, person_id: &Self::PersonId)
#        -> Result<Self::Person, Self::Error>;
#    }
#
#    pub trait Greeter<Context>
#    where
#      Context: PersonContext + ErrorContext,
#    {
#      fn greet(&self, context: &Context, person_id: &Context::PersonId)
#        -> Result<(), Context::Error>;
#    }
  }

  mod simple_greeter {
    use super::traits::{Greeter, NamedPerson, QueryPersonContext};

    pub struct SimpleGreeter;

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
  }

  mod daytime_greeter {
    use super::traits::{
      Greeter, ErrorContext, PersonContext,
      TimeContext, SimpleTime,
    };

    pub struct DaytimeGreeter<InGreeter>(pub InGreeter);

    pub struct ShopClosedError<Time> { time: Time }

    impl<Context, InGreeter, Time, Error, PersonId>
      Greeter<Context> for DaytimeGreeter<InGreeter>
    where
      InGreeter: Greeter<Context>,
      Context: ErrorContext<Error=Error>,
      Context: PersonContext<PersonId=PersonId>,
      Context: TimeContext<Time=Time>,
      Time: SimpleTime,
      Error: From<ShopClosedError<Time>>,
    {
      fn greet(&self, context: &Context, person_id: &PersonId)
        -> Result<(), Error>
      {
        let now = context.now();
        if now.is_daytime() {
          self.0.greet(context, person_id)
        } else {
          Err(ShopClosedError { time: now }.into())
        }
      }
    }
  }

  // ...
}
```

The two greeter components do not depend on each other, but they all depend
on the `traits` crate to make use the abstract definitions. Since these
components do not depend on other crates, they are also _abstract_ components
that can be instantiated with _any_ context types that satisfy the trait
bounds.

Next, we define our concrete `AppContext` struct that implements all
context traits:

```rust
mod app {
  mod traits {
    // ...
#    pub trait NamedPerson {
#      fn name(&self) -> &str;
#    }
#
#    pub trait SimpleTime {
#      fn is_daytime(&self) -> bool;
#    }
#
#    pub trait ErrorContext {
#      type Error;
#    }
#
#    pub trait PersonContext {
#      type PersonId;
#      type Person: NamedPerson;
#    }
#
#    pub trait TimeContext {
#      type Time;
#
#      fn now(&self) -> Self::Time;
#    }
#
#    pub trait QueryPersonContext: PersonContext + ErrorContext {
#      fn query_person(&self, person_id: &Self::PersonId)
#        -> Result<Self::Person, Self::Error>;
#    }
#
#    pub trait Greeter<Context>
#    where
#      Context: PersonContext + ErrorContext,
#    {
#      fn greet(&self, context: &Context, person_id: &Context::PersonId)
#        -> Result<(), Context::Error>;
#    }
  }

  mod simple_greeter {
    // ...
  }

  mod daytime_greeter {
    pub struct ShopClosedError<Time> { time: Time }
    // ...
  }

  mod context {
    use super::traits::*;
    use super::daytime_greeter::ShopClosedError;

    #[derive(Copy, Clone, PartialEq, Eq)]
    pub enum DummyTime {
      DayTime,
      NightTime,
    }

    pub struct BasicPerson {
      name: String,
    }

    pub struct AppContext {
      database: Database,
      time: DummyTime,
    }

    // Database stubs
    struct Database;
    struct DbError;

    pub enum AppError {
      Database(DbError),
      ShopClosed(ShopClosedError<DummyTime>),
      // ...
    }

    impl ErrorContext for AppContext {
      type Error = AppError;
    }

    impl PersonContext for AppContext {
      type PersonId = String;
      type Person = BasicPerson;
    }

    impl TimeContext for AppContext {
      type Time = DummyTime;

      fn now(&self) -> DummyTime {
        self.time
      }
    }

    impl QueryPersonContext for AppContext {
      fn query_person(&self, person_id: &Self::PersonId)
        -> Result<Self::Person, Self::Error>
      {
        unimplemented!() // database stub
      }
    }

    impl NamedPerson for BasicPerson {
      fn name(&self) -> &str {
        &self.name
      }
    }

    impl SimpleTime for DummyTime {
      fn is_daytime(&self) -> bool {
        self == &DummyTime::DayTime
      }
    }

    impl From<ShopClosedError<DummyTime>> for AppError {
      fn from(err: ShopClosedError<DummyTime>) -> Self {
        Self::ShopClosed(err)
      }
    }
  }
}
```

Compared to before, we define a `DummyTime` struct that
mocks the current time with either day time or night time. We then
implement `TimeContext` for `AppContext`, with `DummyTime` being the
`Time` type. We also add `ShopClosedError<DummyTime>` as a variant to
`AppError`, and define a `From` instance for it.

As we can see in this exercise, by having all types used by the greeter
components as abstract types, it becomes very easy to mock up dependencies
like time without having to commit to a specific time library. The explicit
dependencies also help us better understand what features are really needed
from the concrete types. If we know that our application only need the
`SimpleTime` trait, then there are more options out there that we can
try out and switch easily.

It is also worth noting that it doesn't matter whether the concrete types
`AppContext` and `BasicPerson` can have private fields or public fields.
Since the components do not have access to the concrete types, all concrete
fields are essentially private and can only be exposed via trait methods.

Finally, we define an `instances` module to encapsulate the witness of
satisfying all dependencies required from `AppContext` to implement
the `Greeter` components:

```rust
mod app {
  mod traits {
    // ...
#    pub trait NamedPerson {
#      fn name(&self) -> &str;
#    }
#
#    pub trait SimpleTime {
#      fn is_daytime(&self) -> bool;
#    }
#
#    pub trait ErrorContext {
#      type Error;
#    }
#
#    pub trait PersonContext {
#      type PersonId;
#      type Person: NamedPerson;
#    }
#
#    pub trait TimeContext {
#      type Time;
#
#      fn now(&self) -> Self::Time;
#    }
#
#    pub trait QueryPersonContext: PersonContext + ErrorContext {
#      fn query_person(&self, person_id: &Self::PersonId)
#        -> Result<Self::Person, Self::Error>;
#    }
#
#    pub trait Greeter<Context>
#    where
#      Context: PersonContext + ErrorContext,
#    {
#      fn greet(&self, context: &Context, person_id: &Context::PersonId)
#        -> Result<(), Context::Error>;
#    }
  }

  mod simple_greeter {
    // ...
#    use super::traits::{Greeter, NamedPerson, QueryPersonContext};
#
#    pub struct SimpleGreeter;
#
#    impl<Context> Greeter<Context> for SimpleGreeter
#    where
#      Context: QueryPersonContext,
#    {
#      fn greet(&self, context: &Context, person_id: &Context::PersonId)
#        -> Result<(), Context::Error>
#      {
#        let person = context.query_person(person_id)?;
#        println!("Hello, {}", person.name());
#        Ok(())
#      }
#    }
  }

  mod daytime_greeter {
    // ...
#    use super::traits::{
#      Greeter, ErrorContext, PersonContext,
#      TimeContext, SimpleTime,
#    };
#
#    pub struct DaytimeGreeter<InGreeter>(pub InGreeter);
#
#    pub struct ShopClosedError<Time> { time: Time }
#
#    impl<Context, InGreeter, Time, Error, PersonId>
#      Greeter<Context> for DaytimeGreeter<InGreeter>
#    where
#      InGreeter: Greeter<Context>,
#      Context: ErrorContext<Error=Error>,
#      Context: PersonContext<PersonId=PersonId>,
#      Context: TimeContext<Time=Time>,
#      Time: SimpleTime,
#      Error: From<ShopClosedError<Time>>,
#    {
#      fn greet(&self, context: &Context, person_id: &PersonId)
#        -> Result<(), Error>
#      {
#        let now = context.now();
#        if now.is_daytime() {
#          self.0.greet(context, person_id)
#        } else {
#          Err(ShopClosedError { time: now }.into())
#        }
#      }
#    }
  }

  mod context {
    // ...
#    use super::traits::*;
#    use super::daytime_greeter::ShopClosedError;
#
#    #[derive(Copy, Clone, PartialEq, Eq)]
#    pub enum DummyTime {
#      DayTime,
#      NightTime,
#    }
#
#    pub struct BasicPerson {
#      name: String,
#    }
#
#    pub struct AppContext {
#      database: Database,
#      time: DummyTime,
#    }
#
#    // Database stubs
#    struct Database;
#    struct DbError;
#
#    pub enum AppError {
#      Database(DbError),
#      ShopClosed(ShopClosedError<DummyTime>),
#      // ...
#    }
#
#    impl ErrorContext for AppContext {
#      type Error = AppError;
#    }
#
#    impl PersonContext for AppContext {
#      type PersonId = String;
#      type Person = BasicPerson;
#    }
#
#    impl TimeContext for AppContext {
#      type Time = DummyTime;
#
#      fn now(&self) -> DummyTime {
#        self.time
#      }
#    }
#
#    impl QueryPersonContext for AppContext {
#      fn query_person(&self, person_id: &Self::PersonId)
#        -> Result<Self::Person, Self::Error>
#      {
#        unimplemented!() // database stub
#      }
#    }
#
#    impl NamedPerson for BasicPerson {
#      fn name(&self) -> &str {
#        &self.name
#      }
#    }
#
#    impl SimpleTime for DummyTime {
#      fn is_daytime(&self) -> bool {
#        self == &DummyTime::DayTime
#      }
#    }
#
#    impl From<ShopClosedError<DummyTime>> for AppError {
#      fn from(err: ShopClosedError<DummyTime>) -> Self {
#        Self::ShopClosed(err)
#      }
#    }
  }

  mod instances {
    use super::traits::Greeter;
    use super::context::AppContext;
    use super::simple_greeter::SimpleGreeter;
    use super::daytime_greeter::DaytimeGreeter;

    pub fn base_greeter() -> impl Greeter<AppContext> {
      SimpleGreeter
    }

    pub fn app_greeter() -> impl Greeter<AppContext> {
      DaytimeGreeter(base_greeter())
    }
  }
}
```

We first have a `base_greeter` function which witnesses that `SimpleGreeter`
implements `Greeter<AppContext>`. We then define an `app_greeter` function
which witnesses that `DaytimeGreeter<SimpleGreeter>` _also_ implements
`Greeter<AppContext>`.

Notice that in the `app_greeter` body, we construct the greeter with
`DaytimeGreeter(base_greeter())` instead of `DaytimeGreeter(SimpleGreeter)`.
In theory, both expressions are valid and have the same effect. But by calling
`base_greeter` inside `app_greeter`, we are stating that `app_greeter` do
_not_ actually care which concrete type of the base greeter has, aside from
it implementing `Greeter<AppContext>`.

Having separate witness functions can also help us debug any error in
dependencies much more easily. Let's say if we forgot to implement
`QueryPersonContext` for `AppContext`, the dependency for `SimpleGreeter`
would not be satisfied, and we would get a type error in `base_greeter`.
On the other hand, the body of `app_greeter` would not get any error,
because it is not aware of the base greeter being `SimpleGreeter`.

If we were to write the complex expression in one go, like
`DaytimeGreeter(SimpleGreeter)`, it would be less clear which part of the
expression caused the type error. Things would get worse if we have more
complex component composition. Therefore it is always a good practice to
define the component instantiation in multiple smaller functions, so that
it is clear to the reader whether the dependencies are being resolved
correctly.

## Reader Monad

Readers from functional programming background such as Haskellers may notice
that the context pattern look similar to the reader monad pattern. This is
correct, as we are defining a global `Context` type and pass it as a function
argument to all code that requires the context. Additionally, we make use
of the trait (typeclass) system in Rust for compile-time dependency injection,
and the same pattern can be applied for the context type used in reader monads.

For Rust readers, the main difference of the pattern described here with the
reader monad is that we are passing the context value as explicit argument
without using any monadic construct. This is slightly more verbose, but
the benefit is we still get to enjoy much of the benefits of reader monad
without requiring Rust programmers to learn what a monad really is.
(hint: if you know how to use `Result` and `Option`, you might already
understand monad without you knowing it)

## Multiple Context Implementations

We now look at the problem of having multiple context implementations,
and how to deduplicate them. For this we will focus on just implementation
for `QueryPersonContext` that is being used by `SimpleGreeter`.

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

We could implement `QueryPersonContext` for any context type that
contains `FsKvStore` in its field:

```rust
# struct FsKvStore { /* ... */ }
# struct KvStoreError { /* ... */ }
#
# impl FsKvStore {
#   fn get(&self, key: &str) -> Result<Vec<u8>, KvStoreError> {
#     unimplemented!() // stub
#   }
#   // ...
# }
#
# trait ErrorContext {
#   type Error;
# }
#
# trait PersonContext {
#   type PersonId;
#   type Person;
# }
#
# trait QueryPersonContext: PersonContext + ErrorContext {
#   fn query_person(&self, person_id: &Self::PersonId)
#     -> Result<Self::Person, Self::Error>;
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

impl ErrorContext for AppContext {
  type Error = AppError;
}

impl PersonContext for AppContext {
  type PersonId = String;
  type Person = BasicPerson;
}

impl QueryPersonContext for AppContext {
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

Even this simplified version of implementation for `query_person` involves
quite a bit of logic. First, we need to implement serialization logic
to parse `BasicPerson` from raw bytes. We also need to implement the logic
of mapping the namespaced key from the person ID, as well as mapping
the errors in each operation into `AppError`.

Fortunately with the context traits design pattern, components like
`SimpleGreeter` do not need to be aware of how `QueryPersonContext` is
implemented, or the existence of the key-value store in the context.
However, it would still be problematic if we need to re-implement
`QueryPersonContext` for every new context type that we implement.

To avoid copying the body of `query_person` for all context types,
we want to have a _generic_ implementation of `QueryPersonContext`
for _any_ context that has `FsKvStore` in one of its fields.
But if we recall from earlier sections, we already come up with
the design pattern for implementing context-generic components
like `Greeter`. So why not just turn `QueryPersonContext` itself
into a context-generic component?

In fact, with a little re-arrangement, we can redefine
`QueryPersonContext` as `PersonQuerier` as follows:

```rust
# trait ErrorContext {
#   type Error;
# }
#
# trait PersonContext {
#   type PersonId;
#   type Person;
# }
#
trait PersonQuerier<Context>
where
  Context: PersonContext + ErrorContext,
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
# use core::fmt::Display;
#
# struct FsKvStore { /* ... */ }
# struct KvStoreError { /* ... */ }
#
# impl FsKvStore {
#   fn get(&self, key: &str) -> Result<Vec<u8>, KvStoreError> {
#     unimplemented!() // stub
#   }
#   // ...
# }
#
# trait ErrorContext {
#   type Error;
# }
#
# trait PersonContext {
#   type PersonId;
#   type Person;
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
trait KvStoreContext {
  fn kv_store(&self) -> &FsKvStore;
}

struct KvStorePersonQuerier;

impl<Context, PersonId, Person, Error, ParseError>
  PersonQuerier<Context> for KvStorePersonQuerier
where
  Context: KvStoreContext,
  Context: PersonContext<Person=Person, PersonId=PersonId>,
  Context: ErrorContext<Error=Error>,
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
implement `Display`, so that we can format the key as string. Similarly,
we require that `Context::Person` implements `TryFrom<Vec<u8>>`,
and binds the conversion error to an additional type binding `ParseError`.

The above bindings essentially make it possible for `KvStorePersonQuerier`
to work with not only any context that provides `FsKvStore`, but also
any `Context::PersonId` and `Context::Person` types as long as they
implement the `Display` and `TryFrom` traits.

We additionally require `Context::Error` to allow injection of sub-errors
from `KvStoreError` and `ParseError`, so that we can propagate the errors
inside `query_person`.

## Generic Store

We managed to get `KvStorePersonQuerier` we defined earlier to not only
work with a generic context containing an `FsKvStore`, but also work
with any `PersonId` and `Person` types that satisfy some constraints.

We can further generalize the implementation of `KvStorePersonQuerier`
to work with _any_ key-value store implementation. With that, we will
for example be able to swap our store implementation from file-based
to in-memory easily.

```rust
# use core::fmt::Display;
#
# trait ErrorContext {
#   type Error;
# }
#
# trait PersonContext {
#   type PersonId;
#   type Person;
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
trait KvStore: ErrorContext {
  fn get(&self, key: &str) -> Result<Vec<u8>, Self::Error>;
}

trait KvStoreContext {
  type Store: KvStore;

  fn store(&self) -> &Self::Store;
}

struct KvStorePersonQuerier;

impl<Context, Store, PersonId, Person, Error, ParseError, StoreError>
  PersonQuerier<Context> for KvStorePersonQuerier
where
  Context: KvStoreContext<Store=Store>,
  Context: PersonContext<Person=Person, PersonId=PersonId>,
  Context: ErrorContext<Error=Error>,
  Store: KvStore<Error=StoreError>,
  PersonId: Display,
  Person: TryFrom<Vec<u8>, Error=ParseError>,
  Error: From<StoreError>,
  Error: From<ParseError>,
{
  fn query_person(context: &Context, person_id: &PersonId)
    -> Result<Person, Error>
  {
    let key = format!("persons/{}", person_id);

    let bytes = context.store().get(&key)?;

    let person = bytes.try_into()?;

    Ok(person)
  }
}
```

We first define a `KvStore` trait that provides a `get` method for reading
values from the store. It also has `ErrorContext` as its supertrait, so
that we can reuse the `Error` associated type.

We then redefine the `KvStoreContext` to contain an associated type `Store`,
which is required to implement the `KvStore` trait. We then make the
`store` method return a reference to `Self::Store`.

Inside the `PersonQuerier` implementation for `KvStorePersonQuerier`, we
introduce two new explicit type bindings: `Store` for `Context::Store`,
and `StoreError` for `Store::Error`. We also require the main
`Error` type to implement `From<StoreError>`, so that any error from
the store can be propagated.

## Querier Consumer

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
