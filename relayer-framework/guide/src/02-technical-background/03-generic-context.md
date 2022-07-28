# Generic Context

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

At this stage, we have a concrete `Context` struct that contains the database
handle as well as other environment parameters that we may need. However,
`Context` is still concrete, so it is difficult to reuse the `greet` function
in a different context. So let's make the `Context` generic instead:

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

However, since the `Database` type is concrete, it is challenging if we
want to run `greet` with an environment without a database, such as
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

We define a `QueryPersonContext` trait that exposes a method for querying for a
person's details directly from the context. With that, we can have our `greet`
function work with any context type that knows how to query for person details,
regardless of whether it is implemented as a database query.
