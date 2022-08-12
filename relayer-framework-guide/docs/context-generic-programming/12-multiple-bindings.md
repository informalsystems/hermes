# Multiple Type Bindings

When specifying the constraints for indirect depedencies, we have to keep using
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
