# Daytime Greeter

Now suppose that we want to extend our greeter component such that it only
greets a person at day time during office hours. We could directly modify
the `Greeter` implementation for `SimpleGreeter` to do that, but that may
complicate the implementation and makes it more difficult to understand
the core logic. Alternatively, we could define a new `DaytimeGreeter`
component that _wraps_ around the original `SimpleGreeter`.

This new `DaytimeGreeter` component would need to know how to
get the current time of the system, as well as how to tell whether
a given time value is at daytime. Following the context pattern we
learned, we will also define a `HasTime` trait for getting the time:

```rust
trait SimpleTime {
    fn is_daytime(&self) -> bool;
}

trait HasTime {
    type Time;

    fn now(&self) -> Self::Time;
}
```

For demonstration purposes, we first define a `SimpleTime` trait that provides an
`is_daytime` method to tell whether the current time value is considered daytime.
Following that, we define a `HasTime` trait that provides a `now` method
to fetch the current time from the context. Notice that the associated type
`Time` does _not_ implement `SimpleTime`. This is so that we can learn how
to inject the `SimpleTime` constraint as an _indirect dependency_ using the
same dependency injection technique.

We then define the `DaytimeGreeter` component as follows:

```rust
# use std::time::Duration;
#
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
# trait SimpleTime {
#     fn is_daytime(&self) -> bool;
# }
#
# trait HasTime {
#     type Time;
#
#     fn now(&self) -> Self::Time;
# }
#
# trait Greeter<Context>
# where
#     Context: PersonContext + HasError,
# {
#     fn greet(&self, context: &Context, person_id: &Context::PersonId)
#         -> Result<(), Context::Error>;
# }
#
struct DaytimeGreeter<InGreeter>(InGreeter);

impl<Context, InGreeter> Greeter<Context> for DaytimeGreeter<InGreeter>
where
    InGreeter: Greeter<Context>,
    Context: HasTime + PersonContext + HasError,
    Context::Time: SimpleTime,
{
    fn greet(
        &self,
        context: &Context,
        person_id: &Context::PersonId,
    ) -> Result<(), Context::Error>
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

We define the `DaytimeGreeter` with an `InGreeter` type parameter, which
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

## Error Injection

In our earlier implementation of `DaytimeGreeter`, the greeter simply prints
out that the shop has closed, and then returns successfully without calling
the inner greeter. But what if we want `DaytimeGreeter` to return an error
during night time? Since the associated type `Error` in `HasError`
is abstract, there is no obvious way we can construct an error value of
type `Error`.

On the other hand, we learned in the previous section that we can specify an
additional trait bound that `Context::Time` implements `SimpleTime`.
Similarly, we can also specify additional trait bounds for `Context::Error`
so that we gain additional knowledge of how to construct an error value.

We can do this by defining a custom `ShopClosedError` struct and require that
`Context::Error` implement a `From` instance for conversion from `ShopClosedError`:

```rust
# use std::time::Duration;
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
# trait SimpleTime {
#      fn is_daytime(&self) -> bool;
#
#      fn duration_since(&self, other: &Self) -> Duration;
# }
#
# trait HasTime {
#      type Time;
#
#      fn now(&self) -> Self::Time;
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
struct ShopClosedError<Time> { time: Time }

struct DaytimeGreeter<InGreeter>(InGreeter);

impl<Context, InGreeter> Greeter<Context> for DaytimeGreeter<InGreeter>
where
    InGreeter: Greeter<Context>,
    Context: HasTime + PersonContext + HasError,
    Context::Time: SimpleTime,
    Context::Error: From<ShopClosedError<Context::Time>>,
{
    fn greet(
        &self,
        context: &Context,
        person_id: &Context::PersonId,
    ) -> Result<(), Context::Error>
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

The `ShopClosedError` is parameterized by a generic `Time` type so that
it can provide details about the time that caused `ShopClosedError` to be
raised. In the `Greeter` implementation for `DaytimeGreeter` we add an
additional trait bound to require `Context::Error` to implement
`From<ShopClosedError<Context::Time>>`. With that, if the time returned
by `context.now()` is not considered daytime, we can construct a
`ShopClosedError` and turn it into `Context::Error` using the `into` method.

What we have done above is essentially specifying an _error injection method_
for injecting a sub-error type into the main error type. With this, individual
components do not need to know about the concrete application error and all
the possible errors that can be raised. But they can still _inject_ specific
errors into the main error type by requiring additional `From` constraints.

For instance, `DaytimeGreeter` does not need to be aware of whether the inner
greeter component would raise a database error. From the `impl` definition,
we can be confident that `DaytimeGreeter` itself cannot raise any sub-error
other than `ShopClosedError`.

## Multiple Type Bindings

When specifying the constraints for indirect dependencies, we have to keep using
the `Context::` prefix to access associated types like `Context::Error`. Worse,
once we start using nested associated types, we have to resort to using fully
qualified syntax like `<Context::Foo as Foo>::Bar`; `Context::Foo::Bar` doesn't work.

To help simplify the trait bounds for components like `DaytimeGreeter`, we
can use the explicit associated type bindings we learned about earlier:

```rust
# use std::time::Duration;
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
# trait SimpleTime {
#      fn is_daytime(&self) -> bool;
#
#      fn duration_since(&self, other: &Self) -> Duration;
# }
#
# trait HasTime {
#      type Time;
#
#      fn now(&self) -> Self::Time;
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
# struct ShopClosedError<Time> { time: Time }
#
# struct DaytimeGreeter<InGreeter>(InGreeter);
#
impl<Context, InGreeter, Time, Error, PersonId>
    Greeter<Context> for DaytimeGreeter<InGreeter>
where
    InGreeter: Greeter<Context>,
    Context: HasError<Error=Error>,
    Context: PersonContext<PersonId=PersonId>,
    Context: HasTime<Time=Time>,
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
types of the context traits, such as `HasError<Error=Error>`. With the
bindings in place we can have simpler trait bounds like `Time: SimpleTime`
to be specified in place of the more verbose `Context::Time: SimpleTime`.

## Dynamic-Typed Interpretation


```javascript
function daytime_greeter(in_greeter) {
    return function(context, person_id) {
        const now = context.now()
        if now.is_daytime() {
            return in_greeter.greet(context, person_id)
        } else {
            throw new ShopeClosedError({ time: now })
        }
    }
}
```

```javascript
function build_daytime_greeter_class(deps) {
    return Class {
        constructor(in_greeter) {
            this.in_greeter = in_greeter
        }

        greet(context, person_id) {
            const now = deps.HasTime.prototype.now.call(context)
            if deps.HasTime.Time.prototype.is_daytime.call(now) {
                return deps.InGreeter.prototype.greet.call(
                    this.in_greeter, context, person_id)
            } else {
                throw deps.HasError.Error.from(
                    new ShopeClosedError({ time: now }))
            }
        }
    }
}
```

```javascript
const DaytimeGreeter = build_daytime_greeter_class({
    InGreeter: ...,
    HasError: {
        Error: {
            from: function(err) { ... }
        },
    },
    PersonContext: {
        PersonId: ...,
        Person: ...,
    },
    HasTime: {
        Time: {
            prototype: {
                is_daytime: function() { ... }
            }
        }
    },
})
```

```javascript
function build_daytime_greeter_class(deps) {
    const {
        HasTime,
        HasError,
        InGreeter,
    } = deps

    const { Time } = HasTime
    const { Error } = HasError

    return Class {
        constructor(in_greeter) {
            this.in_greeter = in_greeter
        }

        greet(context, person_id) {
            const now = HasTime.prototype.now.call(context)

            if Time.prototype.is_daytime.call(now) {
                return InGreeter.prototype.greet.call(
                    this.in_greeter, context, person_id)
            } else {
                throw Error.from(
                    new ShopeClosedError({ time: now }))
            }
        }
    }
}
```
