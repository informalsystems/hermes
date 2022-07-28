# Multiple Type Bindings

When specifying the constraints for indirect depedencies, we have to keep using
the `Context::` prefix to access associated types like `Context::Error`. Worse,
once we start using nested associated types, we would have to resort to use
fully qualified syntaxes like `<Context::Foo as Foo>::Bar` instead of
`Context::Foo::Bar`.

To help simplify the trait bounds for components like `DaytimeGreeter`, we
can use the explicit associated type bindings we learn earlier:

```rust
# use std::time::Duration;
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
