# Component Composition

Now that we have both `SimpleGreeter` and `DaytimeGreeter` implemented, we
can look at how we can define a full application context that satisfies the
constraints of both greeters. To better structure our application, we also
separate out different parts of the code into separate modules.

First, we put all the abstract traits into a `traits` module:

```rust
mod app {
    mod traits {
        pub trait NamedPerson {
            fn name(&self) -> &str;
        }

        pub trait SimpleTime {
            fn is_daytime(&self) -> bool;
        }

        pub trait HasError {
            type Error;
        }

        pub trait PersonContext {
            type PersonId;
            type Person: NamedPerson;
        }

        pub trait HasTime {
            type Time;

            fn now(&self) -> Self::Time;
        }
    }

    // ...
}
```

This module does not contain any concrete type definitions, and thus has minimal
dependencies on external crates.

In practice, the trait definitions can be placed in different sub-modules so
that we can have more fine grained control over which traits a component depends
on.

Next, we define `SimpleGreeter` and `DaytimeGreeter` in separate modules.

```rust
mod app {
    mod traits {
        // ...
#         pub trait NamedPerson {
#             fn name(&self) -> &str;
#         }
#
#         pub trait SimpleTime {
#             fn is_daytime(&self) -> bool;
#         }
#
#         pub trait HasError {
#             type Error;
#         }
#
#         pub trait PersonContext {
#             type PersonId;
#             type Person: NamedPerson;
#         }
#
#         pub trait HasTime {
#             type Time;
#
#             fn now(&self) -> Self::Time;
#         }
#
#         pub trait PersonQuerier: PersonContext + HasError {
#             fn query_person(&self, person_id: &Self::PersonId)
#                 -> Result<Self::Person, Self::Error>;
#         }
#
#         pub trait Greeter<Context>
#         where
#             Context: PersonContext + HasError,
#         {
#             fn greet(&self, context: &Context, person_id: &Context::PersonId)
#                 -> Result<(), Context::Error>;
#         }
    }

    mod simple_greeter {
        use super::traits::{Greeter, NamedPerson, PersonQuerier};

        pub struct SimpleGreeter;

        impl<Context> Greeter<Context> for SimpleGreeter
        where
            Context: PersonQuerier,
        {
            fn greet(&self, context: &Context, person_id: &Context::PersonId)
                -> Result<(), Context::Error>
            {
                let person = context.query_person(person_id)?;
                println!("Hello, {}", person.name());
                Ok(())
            }
        }
    }

    mod daytime_greeter {
        use super::traits::{
            Greeter, HasError, PersonContext,
            HasTime, SimpleTime,
        };

        pub struct DaytimeGreeter<InGreeter>(pub InGreeter);

        pub struct ShopClosedError<Time> { time: Time }

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
    }

    // ...
}
```

The two greeter components do not depend on each other, but they all depend
on the `traits` crate to make use of the abstract definitions. Since these
components do not depend on other crates, they are also _abstract_ components
that can be instantiated with _any_ context types that satisfy the trait
bounds.

Next, we define our concrete `AppContext` struct that implements all
context traits:

```rust
mod app {
    mod traits {
        // ...
#         pub trait NamedPerson {
#             fn name(&self) -> &str;
#         }
#
#         pub trait SimpleTime {
#             fn is_daytime(&self) -> bool;
#         }
#
#         pub trait HasError {
#             type Error;
#         }
#
#         pub trait PersonContext {
#             type PersonId;
#             type Person: NamedPerson;
#         }
#
#         pub trait HasTime {
#             type Time;
#
#             fn now(&self) -> Self::Time;
#         }
#
#         pub trait PersonQuerier: PersonContext + HasError {
#             fn query_person(&self, person_id: &Self::PersonId)
#                 -> Result<Self::Person, Self::Error>;
#         }
#
#         pub trait Greeter<Context>
#         where
#             Context: PersonContext + HasError,
#         {
#             fn greet(&self, context: &Context, person_id: &Context::PersonId)
#                 -> Result<(), Context::Error>;
#         }
    }

    mod simple_greeter {
        // ...
    }

    mod daytime_greeter {
        pub struct ShopClosedError<Time> { time: Time }
        // ...
    }

    mod context {
        use super::traits::*;
        use super::daytime_greeter::ShopClosedError;

        #[derive(Copy, Clone, PartialEq, Eq)]
        pub enum DummyTime {
            DayTime,
            NightTime,
        }

        pub struct BasicPerson {
            name: String,
        }

        pub struct AppContext {
            database: Database,
            time: DummyTime,
        }

        // Database stubs
        struct Database;
        struct DbError;

        pub enum AppError {
            Database(DbError),
            ShopClosed(ShopClosedError<DummyTime>),
            // ...
        }

        impl HasError for AppContext {
            type Error = AppError;
        }

        impl PersonContext for AppContext {
            type PersonId = String;
            type Person = BasicPerson;
        }

        impl HasTime for AppContext {
            type Time = DummyTime;

            fn now(&self) -> DummyTime {
                self.time
            }
        }

        impl PersonQuerier for AppContext {
            fn query_person(&self, person_id: &Self::PersonId)
                -> Result<Self::Person, Self::Error>
            {
                unimplemented!() // database stub
            }
        }

        impl NamedPerson for BasicPerson {
            fn name(&self) -> &str {
                &self.name
            }
        }

        impl SimpleTime for DummyTime {
            fn is_daytime(&self) -> bool {
                self == &DummyTime::DayTime
            }
        }

        impl From<ShopClosedError<DummyTime>> for AppError {
            fn from(err: ShopClosedError<DummyTime>) -> Self {
                Self::ShopClosed(err)
            }
        }
    }
}
```

Compared to before, we define a `DummyTime` struct that
mocks the current time with either day time or night time. We then
implement `HasTime` for `AppContext`, with `DummyTime` being the
`Time` type. We also add `ShopClosedError<DummyTime>` as a variant to
`AppError` and define a `From` instance for it.

As we can see in this exercise, by having all types used by the greeter
components as abstract types, it becomes very easy to mock up dependencies
such as time functionality without having to commit to a specific time library.
The explicit dependencies also help us better understand what features are
really needed from the concrete types. If we know that our application only needs
the `SimpleTime` trait, then there are more options out there that we can
try out and we can easily swap between them.

It is also worth noting that it doesn't matter whether the concrete types
`AppContext` and `BasicPerson` have private or public fields.
Since the components do not have access to the concrete types, all concrete
fields are essentially private and can only be exposed via trait methods.

Finally, we define an `instances` module to encapsulate the witness of
satisfying all dependencies required from `AppContext` to implement
the `Greeter` components:

```rust
mod app {
    mod traits {
        // ...
#         pub trait NamedPerson {
#             fn name(&self) -> &str;
#         }
#
#         pub trait SimpleTime {
#             fn is_daytime(&self) -> bool;
#         }
#
#         pub trait HasError {
#             type Error;
#         }
#
#         pub trait PersonContext {
#             type PersonId;
#             type Person: NamedPerson;
#         }
#
#         pub trait HasTime {
#             type Time;
#
#             fn now(&self) -> Self::Time;
#         }
#
#         pub trait PersonQuerier: PersonContext + HasError {
#             fn query_person(&self, person_id: &Self::PersonId)
#                 -> Result<Self::Person, Self::Error>;
#         }
#
#         pub trait Greeter<Context>
#         where
#             Context: PersonContext + HasError,
#         {
#             fn greet(&self, context: &Context, person_id: &Context::PersonId)
#                 -> Result<(), Context::Error>;
#         }
    }

    mod simple_greeter {
        // ...
#         use super::traits::{Greeter, NamedPerson, PersonQuerier};
#
#         pub struct SimpleGreeter;
#
#         impl<Context> Greeter<Context> for SimpleGreeter
#         where
#             Context: PersonQuerier,
#         {
#             fn greet(&self, context: &Context, person_id: &Context::PersonId)
#                 -> Result<(), Context::Error>
#             {
#                 let person = context.query_person(person_id)?;
#                 println!("Hello, {}", person.name());
#                 Ok(())
#             }
#         }
    }

    mod daytime_greeter {
        // ...
#         use super::traits::{
#             Greeter, HasError, PersonContext,
#             HasTime, SimpleTime,
#         };
#
#         pub struct DaytimeGreeter<InGreeter>(pub InGreeter);
#
#         pub struct ShopClosedError<Time> { time: Time }
#
#         impl<Context, InGreeter, Time, Error, PersonId>
#             Greeter<Context> for DaytimeGreeter<InGreeter>
#         where
#             InGreeter: Greeter<Context>,
#             Context: HasError<Error=Error>,
#             Context: PersonContext<PersonId=PersonId>,
#             Context: HasTime<Time=Time>,
#             Time: SimpleTime,
#             Error: From<ShopClosedError<Time>>,
#         {
#             fn greet(&self, context: &Context, person_id: &PersonId)
#                 -> Result<(), Error>
#             {
#                 let now = context.now();
#                 if now.is_daytime() {
#                     self.0.greet(context, person_id)
#                 } else {
#                     Err(ShopClosedError { time: now }.into())
#                 }
#             }
#         }
    }

    mod context {
        // ...
#         use super::traits::*;
#         use super::daytime_greeter::ShopClosedError;
#
#         #[derive(Copy, Clone, PartialEq, Eq)]
#         pub enum DummyTime {
#             DayTime,
#             NightTime,
#         }
#
#         pub struct BasicPerson {
#             name: String,
#         }
#
#         pub struct AppContext {
#             database: Database,
#             time: DummyTime,
#         }
#
#         // Database stubs
#         struct Database;
#         struct DbError;
#
#         pub enum AppError {
#             Database(DbError),
#             ShopClosed(ShopClosedError<DummyTime>),
#             // ...
#         }
#
#         impl HasError for AppContext {
#             type Error = AppError;
#         }
#
#         impl PersonContext for AppContext {
#             type PersonId = String;
#             type Person = BasicPerson;
#         }
#
#         impl HasTime for AppContext {
#             type Time = DummyTime;
#
#             fn now(&self) -> DummyTime {
#                 self.time
#             }
#         }
#
#         impl PersonQuerier for AppContext {
#             fn query_person(&self, person_id: &Self::PersonId)
#                 -> Result<Self::Person, Self::Error>
#             {
#                 unimplemented!() // database stub
#             }
#         }
#
#         impl NamedPerson for BasicPerson {
#             fn name(&self) -> &str {
#                 &self.name
#             }
#         }
#
#         impl SimpleTime for DummyTime {
#             fn is_daytime(&self) -> bool {
#                 self == &DummyTime::DayTime
#             }
#         }
#
#         impl From<ShopClosedError<DummyTime>> for AppError {
#             fn from(err: ShopClosedError<DummyTime>) -> Self {
#                 Self::ShopClosed(err)
#             }
#         }
    }

    mod instances {
        use super::traits::Greeter;
        use super::context::AppContext;
        use super::simple_greeter::SimpleGreeter;
        use super::daytime_greeter::DaytimeGreeter;

        pub fn base_greeter() -> impl Greeter<AppContext> {
            SimpleGreeter
        }

        pub fn app_greeter() -> impl Greeter<AppContext> {
            DaytimeGreeter(base_greeter())
        }
    }
}
```

We first have a `base_greeter` function which witnesses that `SimpleGreeter`
implements `Greeter<AppContext>`. We then define an `app_greeter` function
which witnesses that `DaytimeGreeter<SimpleGreeter>` _also_ implements
`Greeter<AppContext>`.

Notice that in the `app_greeter` body, we construct the greeter with
`DaytimeGreeter(base_greeter())` instead of `DaytimeGreeter(SimpleGreeter)`.
In theory, both expressions are valid and have the same effect, but calling
`base_greeter` inside `app_greeter` implies that `app_greeter` does not care
what the concrete type of `base_greeter` is; all that matters is that it
implements `Greeter<AppContext>`.

Having separate witness functions can also help us debug any errors that arise
in dependencies much more easily. Let's say that we forgot to implement
`PersonQuerier` for `AppContext` such that the dependency for
`SimpleGreeter` would not be satisfied; we would get a type error in
`base_greeter`. However, no errors would crop up in `app_greeter`,
because it doesn't care that base greeter implements `SimpleGreeter`.

If we were to write the complex expression in one go, like
`DaytimeGreeter(SimpleGreeter)`, it would be less clear which part of the
expression caused the type error. Things would get worse if we introduced more
complex component composition. Therefore, it is always a good practice to
define the component instantiation in multiple smaller functions so that
it is clear to the reader whether the dependencies are being resolved
correctly.

## Component Graph Visualization

<a href="https://app.excalidraw.com/l/4XqkU6POmGI/2PCintQJN3m" target="_blank">
    <div style="pointer-events: none;">
        <embed src="../images/daytime-greeter-graph.svg"
            width="100%"
        />
    </div>
</a>



## Reader Monad

Readers coming from a functional programming background might notice
that the context pattern looks similar to the reader monad pattern. This is
correct, as we are defining a global `Context` type and passing it around as a
function argument to all code that requires the context. Additionally, we make
use of the trait (typeclass) system in Rust for compile-time dependency
injection, and the same pattern can be applied for the context type used in
reader monads.

For Rust readers, the main difference of the pattern described here with the
reader monad is that we are passing the context value as an explicit argument
without making use of any monadic constructs. Doing it this way is slightly more
verbose, but the upside is that we still get to enjoy much of the benefits of
the reader monad pattern without requiring Rust programmers to learn what a
monad really is (though if you're comfortable with using `Result` and `Option`,
you've already been making use of monads).
