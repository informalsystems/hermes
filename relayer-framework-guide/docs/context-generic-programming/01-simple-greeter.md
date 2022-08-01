# Simple Greeter

Let's say we want to write a simple greeter program that greets a person.
The simplest way is to write a function like follows:

```rust
fn greet(name: String) {
  println!("Hello, {}!", name);
}
```

When calling the `greet` function from a larger context, we may want to pass
a `Person` struct with a `name` attribute on it, so that the caller does not
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

But the caller of the `greet` function might not have the person's information
on hand, as it may be stored in a database. So we might want to implement
a `greet` function that accepts a `PersonId` and a database handler, so that
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
quickly even with such a simple example:

- The full details of the `Person` struct must be fetched regardless of
  whether the `greet` function needs it.
- The concrete implementation of `Database` is exposed to the greet function,
  making it difficult to work with other databases.
- The concrete error `DbError` from the database query is leaked into the
  `greet` function implementation.

When the application is still in its early stages, it might be tempting to
leave these concerns aside and not worry about them too much. But eventually,
we will reach a point where we need our application to work with different
implementations. For example:

- We may want a caching layer to cache the person's information instead of
  querying directly from the database all the time.
- We may want to have different database implementations, such as a mocked-up
  database or an in-memory database.
- We may want to have multiple concrete person types, so that the database
  only fetches the essential information. e.g. `PersonWithName`,
  `PersonWithFullDetails`, `PersonWithRoles` etc.
