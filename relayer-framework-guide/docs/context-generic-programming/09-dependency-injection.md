# Compile-Time Dependency Injection

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

This pattern of making use of Rust's trait system for depedency injection
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
