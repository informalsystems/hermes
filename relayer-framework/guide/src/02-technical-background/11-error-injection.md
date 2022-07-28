# Error Injection

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
