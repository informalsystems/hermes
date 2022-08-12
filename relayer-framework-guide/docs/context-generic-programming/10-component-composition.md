# Component Composition

Now suppose that we want to extend our greeter component such that it only
greets a person at day time during office hours. We could directly modify
the `Greeter` implementation for `SimpleGreeter` to do that, but that may
complicate the implementation and makes it more difficult to understand
the core logic. Alternatively, we could define a new `DaytimeGreeter`
component that _wraps_ around the original `SimpleGreeter`.

This new `DaytimeGreeter` component would need to know how to
get the current time of the system, as well as how to tell whether
a given time value is at daytime. Following the context pattern we
learned, we will also define a `HasTime` trait for getting the time.

The full implementation is as follows:

```rust
# use std::time::Duration;
#
# trait NamedPerson {
#   fn name(&self) -> &str;
# }
#
# trait HasError {
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

trait HasTime {
  type Time;

  fn now(&self) -> Self::Time;
}

trait Greeter<Context>
where
  Context: PersonContext + HasError,
{
  fn greet(&self, context: &Context, person_id: &Context::PersonId)
    -> Result<(), Context::Error>;
}

struct DaytimeGreeter<InGreeter>(InGreeter);

impl<Context, InGreeter> Greeter<Context> for DaytimeGreeter<InGreeter>
where
  InGreeter: Greeter<Context>,
  Context: HasTime + PersonContext + HasError,
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

For demonstration purposes, we first define a `SimpleTime` trait that provides an
`is_daytime` method to tell whether the current time value is considered daytime.
Following that, we define a `HasTime` trait that provides a `now` method
to fetch the current time from the context. Notice that the associated type
`Time` does _not_ implement `SimpleTime`. This is so that we can learn how
to inject the `SimpleTime` constraint as an _indirect dependency_ using the
same dependency injection technique.

We then define the `DaytimeGreeter` with an `InGreeter` type parameter, which
would act as the inner `Greeter` component. We then define a generic
implementation of `Greeter<Context>` for `DaytimeGreeter<InGreeter>`.
In the trait bounds, we require the inner greeter `InGreeter` to also
implement `Greeter<Context>`, since the core logic is implemented over there.

Aside from `PersonContext` and `HasError`, we also require `Context`
to implement `HasTime` for `DaytimeGreeter` to fetch the current time.
Other than that, we also explicitly require that the associated type
`Context::Time` implements `SimpleTime`.

By specifying `SimpleTime` as an explicit dependency, we relax the requirement
of how the `HasTime` trait can be used by other components. So if
`SimpleTime` is only ever used by `DaytimeGreeter`, and if an application
does not need `DaytimeGreeter`, then a concrete context can skip implementing
`SimpleTime` for its time type, even if the trait `HasTime` is used by
other components.
