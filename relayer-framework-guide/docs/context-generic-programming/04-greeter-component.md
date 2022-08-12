# Greeter Component

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
trait Greeter<Context>
where
    Context: PersonContext + HasError,
{
    fn greet(
        &self,
        context: &Context,
        person_id: &Context::PersonId,
    ) -> Result<(), Context::Error>;
}

struct SimpleGreeter;

impl<Context> Greeter<Context> for SimpleGreeter
where
    Context: PersonQuerier,
{
    fn greet(
        &self,
        context: &Context,
        person_id: &Context::PersonId,
    ) -> Result<(), Context::Error>
    {
        let person = context.query_person(person_id)?;
        println!("Hello, {}", person.name());
        Ok(())
    }
}
```

The `Greeter` trait is defined to be parameterized by a generic `Context` type,
which is required to implement both `PersonContext` and `HasError`.
The `greet` method is then defined without generic parameters, as these have been
captured in the trait definition. We then define an empty struct `SimpleGreeter`,
which is there only to implement the `Greeter` trait for any `Context` type
that implements `PersonQuerier`.

It is worth noticing here that in the main `Greeter` trait definition,
the `Context` type, is only required to implement `PersonContext` and
`HasError`, but there is no mention of the `PersonQuerier`
trait bound. On the other hand, the concrete `Greeter` implementation
for `SimpleGreeter` can require the additional trait bound
`Context: PersonQuerier` in its `impl` definition.

This demonstrates the benefits of separating the `PersonQuerier`
from the `PersonContext` trait: From the perspective of a consumer
that uses the `Greeter` component, it does not need to know whether
the generic context type implements `PersonQuerier`. This means
that from the trait bounds alone, we can tell whether a piece of code
can call `query_person` directly, or whether it can only call the
`greet` method to greet a person without knowing how the greeter determined
the person's name.


## Greeter Instance

In the previous chapter, we defined `AppContext` as a concrete implementation
for the context traits `HasError`, `PersonContext`, and `PersonQuerier`.
Based on the earlier definition of `SimpleGreeter` and its `Greeter`
implementation, we can deduce that `SimpleGreeter` should implement
`Greeter<AppContext>`.

But how can we ensure that we implemented `AppContext` correctly to be used by
`SimpleGreeter`? If we forgot to implement any dependency that is required by
`SimpleGreeter`, such as `PersonQuerier`, we would get a compile-time error
when trying to use `SimpleGreeter` as `Greeter<AppContext>`. Worse, if we try
to use `SimpleGreeter` within another generic component, the error messages
may become too incomprehensible to find out what went wrong.

In test-driven development, it is common practice that we would write _tests_
that check that our code satisfies certain requirements and constraints.
Following the same principle, we would want to write tests that check that
`SimpleGreeter` does implements `Greeter<AppContext>`. But instead of writing
_dynamic tests_ that checks for the program behavior at runtime, we can write
_static tests_ that checks that the program requirements are satisfied at
_compile time_.


Our test would be implemented as an `app_greeter` function which checks at
_compile time_ that `SimpleGreeter` implements `Greeter<AppContext>`:

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
# trait Greeter<Context>
# where
#      Context: PersonContext + HasError,
# {
#      fn greet(&self, context: &Context, person_id: &Context::PersonId)
#          -> Result<(), Context::Error>;
# }
#
# struct SimpleGreeter;
#
# impl<Context> Greeter<Context> for SimpleGreeter
# where
#      Context: PersonQuerier,
# {
#      fn greet(&self, context: &Context, person_id: &Context::PersonId)
#          -> Result<(), Context::Error>
#      {
#          let person = context.query_person(person_id)?;
#          println!("Hello, {}", person.name());
#          Ok(())
#      }
# }
# struct BasicPerson {
#     name: String,
# }
#
# impl NamedPerson for BasicPerson {
#     fn name(&self) -> &str {
#         &self.name
#     }
# }
#
# struct AppContext {
#     database: Database,
# }
#
# // Database stubs
# struct Database;
# struct DbError;
#
# enum AppError {
#     Database(DbError),
#     // ...
# }
#
# impl HasError for AppContext {
#     type Error = AppError;
# }
#
# impl PersonContext for AppContext {
#     type PersonId = String;
#     type Person = BasicPerson;
# }
#
# impl PersonQuerier for AppContext {
#     fn query_person(&self, person_id: &Self::PersonId)
#         -> Result<Self::Person, Self::Error>
#     {
#         unimplemented!() // database stub
#     }
# }
#
fn app_greeter() -> impl Greeter<AppContext> {
    SimpleGreeter
}
```

Our `app_greeter` function accepts nothing and returns `impl Greeter<AppContext>`.
This indicates that the function can return a value with an _existential type_
that implements `Greeter<AppContext>`. Inside the function body, we simply
return a `SimpleGreeter` value. From the surface, it may look like this
is effectively the same as the function with signature
`fn app_greeter() -> SimpleGreeter`. But by returning `impl Greeter<AppContext>`,
we force the Rust compiler to check here that `SimpleGreeter` must
implement `Greeter<AppContext>`.

Having `app_greeter` compiled successfully is sufficient to prove that
`SimpleGreeter` can _always_ be used as a `Greeter<AppContext>`. Hence, we can
say that `app_greeter` is a _proof_ that `SimpleGreeter: Greeter<AppContext>`.

We call static tests like `app_greeter` as proofs, as it works similar to
writing mathematical proofs as programs in _dependent-typed programming_.
In this style of programming,the type-checking of a program alone is sufficient
to prove that a given requirement is _always_ satisfied, without us having to
_execute_ the program.
This is much more efficient as compared to dynamic checking, which can only
check for requirements at runtime and raise errors when the requirements
are not satisfied.

## Compile-Time Dependency Injection

The `app_greeter` function demonstrates a form of _dependency injection_
done at compile time. This is because for any code to use a type implementing
`Greeter<Context>`, they only need to know that `Context` implements
`HasError` and `PersonContext`. But to make `SimpleGreeter` implement
`Greeter<Context>`, it also needs `Context` to implement `PersonQuerier`.

When we return `SimpleGreeter` inside `app_greeter`, the Rust compiler
figures out that `SimpleGreeter` requires `AppContext` to implement
`PersonQuerier`. It would then try to automatically _resolve_ the
dependency by searching for an implementation of `PersonQuerier`
for `AppContext`. Upon finding the implementation, Rust "binds" that
implementation with `SimpleGreeter` and returns it as an existential
type that implements `Greeter<AppContext>`. As a result,
we can treat the type returned from `app_greeter` as an abstract type,
and "forget" the fact that `AppContext` implements `PersonQuerier`.

This pattern of making use of Rust's trait system for dependency injection
efficiently solves the
[context and capabilities problem](https://tmandry.gitlab.io/blog/posts/2021-12-21-context-capabilities/)
in Rust. Without it, we would have to rely on more exotic language features
that are not available in Rust, or resort to manually passing dependencies
around by hand.

For example, we could perform manual binding for an implementation similar
to `SimpleGreeter` as a purely generic function as follows:

```rust
# trait NamedPerson {
#      fn name(&self) -> &str;
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
system, the Rust compiler handles the binding of dependencies automatically in
a manner similar to what is being done in the example above. The binding process
is not only automated, the code that the compiler generates is also much more
efficient. Because the binding is done at compile time, the Rust compiler is
able to perform many further optimizations, such as code inlining.

As we will see later, this process of automatic resolution can be applied to
_nested_ dependencies. Thanks to how the trait system works, we can specify
complex dependencies for our components and have the Rust compiler figure out
how to stitch together the dependencies and construct the combined components
that we need.
