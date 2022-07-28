# Component Composition

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
