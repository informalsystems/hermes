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

struct Database { /* ... */ }
struct DbError { /* ... */ }

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

## Comparison with Dynamic Typing

One thing worth noting with our `greet` example in Rust is that many of the
problems mentioned are applicable because we are programming in a statically-typed
language. If we were to re-implement the `greet` function in a dynamically-
typed language like JavaScript, many of these problems go away:

```javascript
function greet(db, personId) {
    const person = db.queryPerson(personId)
    console.log(`Hello, ${person.name}!`)
}
```

Thanks to dynamic typing, the JavaScript `greet` function above is general
in several ways:

- The function can work with any `db` value, as long as it provides a valid
    `query_person` method.
- The function can work with any `person` value returned from `db.query_person`,
    as long as it contains a `name` field that can be converted into a string.
- The error can be thrown implicitly by `db.query_person` as an exception.

On the upside, the dynamic nature of the `greet` function means that it can
easily be reused across multiple database and person implementations. On the
downside, since there is no type information, it is easy to accidentally call
`greet` with invalid implementations and only discover the errors late during
runtime execution.

Ideally, we would like to have the same benefits of writing generalized programs
in dynamically-typed contexts, but still enjoy the benefits of type checking when there are
mismatches in the specialized implementation.

## Dynamic Context

The first thing to notice when writing generalized functions is that there are
usually contextual values in the surrounding environment that are needed for
the program to execute successfully.

In our dynamic `greet` example, we can generalize the `db` value and think of it
as a `context` value, which may contain other environment parameters such as
what kind of greeting is used.

```javascript
function greet(context, personId) {
    const person = context.queryPerson(personId)
    const greeting = context.getGreeting()
    console.log(`${greeting}, ${person.name}!`)
}
```

In the OOP world, the `context` value is typically referred to as a `this` or `self`
value. However, for clarity and for more structured composition, it is better
to think of it as a fully abstract value with unknown type. This allows the
context value to be augmented in a functional way, without having to resort to
using any OOP class hierarchy.
