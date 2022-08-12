# Comparison with Dynamic Typing

One thing worth noting with our `greet` example in Rust is that many of the
problems mentioned are applicable because we are programming in a statically-typed
language. If we were to re-implement the `greet` function in a dynamically-
typed language like JavaScript, many of these problems go away:

```javascript
function greet(db, personId) {
    const person = db.queryPerson(personId)
    console.log(`Hello, ${person.name}!`)
}
```

Thanks to dynamic typing, the JavaScript `greet` function above is general
in several ways:

- The function can work with any `db` value, as long as it provides a valid
    `query_person` method.
- The function can work with any `person` value returned from `db.query_person`,
    as long as it contains a `name` field that can be converted into a string.
- The error can be thrown implicitly by `db.query_person` as an exception.

On the upside, the dynamic nature of the `greet` function means that it can
easily be reused across multiple database and person implementations. On the
downside, since there is no type information, it is easy to accidentally call
`greet` with invalid implementations and only discover the errors late during
runtime execution.

Ideally, we would like to have the same benefits of writing generalized programs
in dynamically-typed contexts, but still enjoy the benefits of type checking when there are
mismatches in the specialized implementation.

## Dynamic Context

The first thing to notice when writing generalized functions is that there are
usually contextual values in the surrounding environment that are needed for
the program to execute successfully.

In our dynamic `greet` example, we can generalize the `db` value and think of it
as a `context` value, which may contain other environment parameters such as
what kind of greeting is used.

```javascript
function greet(context, personId) {
    const person = context.queryPerson(personId)
    const greeting = context.getGreeting()
    console.log(`${greeting}, ${person.name}!`)
}
```

In the OOP world, the `context` value is typically referred to as a `this` or `self`
value. However, for clarity and for more structured composition, it is better
to think of it as a fully abstract value with unknown type. This allows the
context value to be augmented in a functional way, without having to resort to
using any OOP class hierarchy.
