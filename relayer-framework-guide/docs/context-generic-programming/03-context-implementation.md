# Context Implementation

With the basic traits implemented, we now look at how we can define a
concrete context that satisfies the traits:

```rust
# trait NamedPerson {
#      fn name(&self) -> &str;
# }
#
# trait HasError {
#      type Error;
# }
#
# trait PersonContext {
#      type PersonId;
#      type Person: NamedPerson;
# }
#
# trait PersonQuerier: PersonContext + HasError {
#      fn query_person(&self, person_id: &Self::PersonId)
#          -> Result<Self::Person, Self::Error>;
# }
#
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

impl HasError for AppContext {
    type Error = AppError;
}

impl PersonContext for AppContext {
    type PersonId = String;
    type Person = BasicPerson;
}

impl PersonQuerier for AppContext {
    fn query_person(&self, person_id: &Self::PersonId)
        -> Result<Self::Person, Self::Error>
    {
        unimplemented!() // database stub
    }
}
```

We first define a `BasicPerson` struct with only a `name` field,
since that is the minimal information required for `greet` to work.
We implement `NamedPerson` for `BasicPerson`, by simply returning
`&self.name`.

We also define an `AppContext` struct with a stub database field.
For demonstration purposes, we have a dummy `Database` struct, and a `DbError`
type to represent database errors. We also define an `AppError`
enum to represent all application errors, with one of them being
`DbError`.

We implement `HasError` for `AppContext`, with `AppError` as
the `Error` type. We also implement `PersonContext` for `AppContext`,
with the `PersonId` associated type being `String` and the `Person`
associated type being `BasicPerson`. We also implement `PersonQuerier`
but leave the `query_person` as a stub for performing database queries
in an actual application.
