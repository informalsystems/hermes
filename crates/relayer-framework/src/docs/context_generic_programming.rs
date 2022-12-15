/*!
   # A Crash Course on Context-Generic Programming

   This section provides a quick introduction to context-generic programming,
   which is a programming technique that is used heavily by the IBC relayer
   framework. For a more gentle and complete introduction to context-generic
   programming, check out our full tutorial on
   [context-generic programming](https://informalsystems.github.io/context-generic-programming/).

   In its essence, context-generic programming takes regular methods
   implemented in object-oriented programming (OOP) style, and turn
   them into modular components that can work over a generic context.

   For example, consider the following OOP-style code:

   ```rust
   # mod example {
   pub mod provider {
       pub struct AppContext { /* ... */ }
       impl AppContext {
           pub fn perform_action(&self, /* ... */) {
               # unimplemented!()
               /* ... */
           }

           pub fn perform_another_action(&self, /* ... */) {
               # unimplemented!()
               /* ... */
           }
       }
   }

   mod consumer {
       # use super::provider::AppContext;
       fn do_something(context: AppContext, /* .... */) {
           /* ... */
           context.perform_action(/* ... */);
           /* ... */
       }
   }
   # }
   ```

   We have a `provider` module that implements a concrete `AppContext` type,
   and two public methods, `perform_action`, and `perform_another_action`.
   Other than that, we also have a `consumer` module that uses the `AppContext`
   type provided by the `provider` module, as well as the `perform_action`
   method.

   In practice, the `provider` and `consumer` modules may be different crates,
   developed by different teams. However the use of the `AppContext` type and the
   `perform_action` method tightly couples the `consumer` module with the
   provider module. This may come with many downsides, in particular if the
   `AppContext` type implemented by the `provider` module is very complex.
   Aside from `perform_action`, the `provider` module may also implement
   many other methods, which the `consumer` module do not really need,
   such as `perform_another_action`.

   Context-generic programming offers a way to break down the monolithic design
   of provider methods, and turn them into modular components that can be
   selectively chosen by the consumers. Furthermore, the concrete context type
   is replaced with a generic context parameter, so that different context
   types can be used to implement the components depending on the subset of
   components that are needed by the consumers.

   ## Consumer and Provider Traits

   With context-generic programming, we would first define the following traits
   that correspond to the original `perform_action` method:

   ```
   trait CanPerformAction {
       fn perform_action(&self, /* ... */);
   }

   trait ActionPerformer<Context> {
       fn perform_action(context: &Context, /* ... */);
   }
   ```

   The `CanPerformAction` trait is a _consumer_ trait that is designed to
   be used by _consumers_ of a component. On the other hand, the `ActionPerformer`
   trait is a _provider_ trait that is designed to be used by _implementers_
   of a component.

   If we carefully contrast between the two traits, the main difference is
   that in the consumer trait `CanPerformAction`, there is an implicit `Self`
   type and a `&self` parameter. On the other hand, the provider trait
   `ActionPerformer` has an explicit `Context` type parameter and a `context`
   argument, which corresponds to the self parameters in the `CanPerformAction`
   trait.

   In context-generic programming, we have a separation of consumer and
   provider traits to separate the concerns of _using_ a component as
   compared to _implementing_ a component. By doing so, we can allow
   multiple implementations of a component to co-exist, while the users
   of a component can assume that a generic context always provide
   exactly one unique implementation of a component.

   ## Using a Consumer Trait

   We first look at how the `consumer` module can be modified to use the
   consumer trait `CanPerformAction`.

   ```
   mod consumer {
       # trait CanPerformAction {
       #     fn perform_action(&self, /* ... */);
       # }
       fn do_something<Context>(context: Context, /* .... */)
       where
           Context: CanPerformAction,
       {
           /* ... */
           context.perform_action(/* ... */);
           /* ... */
       }
   }
   ```

   Instead of using a concrete context directly, our consumer function is now
   defined to be generic over any `Context` type, given that `Context`
   implements `CanPerformAction`. Since the consumer trait `CanPerformAction`
   makes refers to `Context` as `Self`, the consumer can call
   `context.perform_action()` the same way as it did in the original OOP-style
   program.

   ## Implementing a Provider Trait

   We now look at how a `provider` module can implement the action performer
   component:

   ```
   mod provider {
       # trait HasRequirementsToPerformSimpleAction {}
       # trait ActionPerformer<Context> {
       #     fn perform_action(context: &Context, /* ... */);
       # }
       struct PerformSimpleAction;
       impl<Context> ActionPerformer<Context> for PerformSimpleAction
       where
           Context: HasRequirementsToPerformSimpleAction,
       {
           fn perform_action(context: &Context, /* ... */) {
               # unimplemented!()
               /* ... */
           }
       }
   }
   ```

   The `provider` module first defines a `PerformSimpleAction` struct, which
   is used to represent an implementation of the action performer component
   at the _type level_.

   We then implement `ActionPerformer<Context>` for `PerformSimpleAction`,
   for any generic `Context` type, as long as the type satisfies some requirements
   as specified in `HasRequirementsToPerformSimpleAction`.

   One thing worth noting is that the constraint `HasRequirementsToPerformSimpleAction`
   is _hidden_ behind the `impl` definition, as it is not shown in the
   `ActionPerformer` trait itself.
   Essentially, we have made use of the properties of Rust's trait system
   to perform _dependency injection_ to propagate the constraints of
   a particular implementation without polluting the trait signature of
   either the producer or consumer traits.

   ## Linking Consumer and Provider traits

   At this stage, the `provider` module has defined a generic implementation
   of `PerformSimpleAction`, but it has yet to implement `CanPerformAction`
   for its concrete `AppContext`. We can now implement `CanPerformAction`
   as follows:

   ```
   pub mod provider {
       # trait HasRequirementsToPerformSimpleAction {}
       # trait CanPerformAction {
       #     fn perform_action(&self, /* ... */);
       # }
       # trait ActionPerformer<Context> {
       #     fn perform_action(context: &Context, /* ... */);
       # }
       # struct PerformSimpleAction;
       # impl<Context> ActionPerformer<Context> for PerformSimpleAction
       # where
       #     Context: HasRequirementsToPerformSimpleAction,
       # {
       #     fn perform_action(context: &Context, /* ... */) {
       #         unimplemented!()
       #         /* ... */
       #     }
       # }
       pub struct AppContext { /* ... */ }
       impl HasRequirementsToPerformSimpleAction for AppContext { /* ... */ }

       impl CanPerformAction for AppContext {
           fn perform_action(&self, /* ... */) {
               PerformSimpleAction::perform_action(self, /* ... */)
           }
       }
   }
   ```

   We first ensure that the concrete type `AppContext` implements the
   requirements that are needed to call `PerformSimpleAction`, such as by
   implementing `HasRequirementsToPerformSimpleAction`. We then implement
   `CanPerformAction` by simply forwarding to the call to
   `PerformSimpleAction::perform_action`.

   ## Benefits of separating provider and consumer traits

   A benefit of separating the actual implementation of a provider
   trait from the implementation of a consumer trait is that we can
   reuse the same provider implementation on other consumer trait
   implementations. For example, let's say the provider defines
   a second concrete context `AnotherAppContext`, it would then
   still able to reuse `PerformSimpleAction` without having to
   copy the entire implementation code:

   ```
   pub mod provider {
       # trait HasRequirementsToPerformSimpleAction {}
       # trait CanPerformAction {
       #     fn perform_action(&self, /* ... */);
       # }
       # trait ActionPerformer<Context> {
       #     fn perform_action(context: &Context, /* ... */);
       # }
       # struct PerformSimpleAction;
       # impl<Context> ActionPerformer<Context> for PerformSimpleAction
       # where
       #     Context: HasRequirementsToPerformSimpleAction,
       # {
       #     fn perform_action(context: &Context, /* ... */) {
       #         unimplemented!()
       #         /* ... */
       #     }
       # }
       pub struct AnotherAppContext { /* ... */ }
       # impl HasRequirementsToPerformSimpleAction for AnotherAppContext { /* ... */ }
       impl CanPerformAction for AnotherAppContext {
           fn perform_action(&self, /* ... */) {
               PerformSimpleAction::perform_action(self, /* ... */)
           }
       }
   }
   ```

   The separation also allows us to easily switch between different provider
   components. For example, let's say there is another implementation of
   `ActionPerformer`, `PerformComplexAction` that can be used by contexts
   that implement additional requirements `HasAdditionalRequirementsToPerformAction`.
   If the provider's `AppContext` satisfies the additional requirements,
   we can then switch to the other component with a single line change:

   ```
   pub mod provider {
       # trait HasAdditionalRequirementsToPerformAction {}
       # trait CanPerformAction {
       #     fn perform_action(&self, /* ... */);
       # }
       # trait ActionPerformer<Context> {
       #     fn perform_action(context: &Context, /* ... */);
       # }
       # struct PerformComplexAction;
       # impl<Context> ActionPerformer<Context> for PerformComplexAction
       # where
       #     Context: HasAdditionalRequirementsToPerformAction,
       # {
       #     fn perform_action(context: &Context, /* ... */) {
       #         unimplemented!()
       #         /* ... */
       #     }
       # }
       pub struct AppContext { /* ... */ }
       impl HasAdditionalRequirementsToPerformAction for AppContext { /* ... */ }

       impl CanPerformAction for AppContext {
           fn perform_action(&self, /* ... */) {
               PerformComplexAction::perform_action(self, /* ... */)
           }
       }
   }
   ```

   ## Dual roles of providers and consumers

   A key idea in context-generic programming is that components can be
   _both_ provider and consumers at the same time.

   For example, instead of having the `consumer` module to define a function
   `do_something` that is generic over a context, we can turn the generic function
   into a context-generic component. After all, the function `do_something`
   is in fact a provider for some other modules that call that function.

   Our `consumer` module can as introduce a new something-doer component follows:

   ```
   mod consumer {
       # trait CanPerformAction {
       #     fn perform_action(&self, /* ... */);
       # }
       # trait HasRequirementsToDoSomethingSmart {}
       trait CanDoSomething {
           fn do_something(&self, /* ... */);
       }
       trait SomethingDoer<Context> {
           fn do_something(context: &Context, /* ... */);
       }

       struct DoSomethingSmart;
       impl<Context> SomethingDoer<Context> for DoSomethingSmart
       where
           Context: CanPerformAction,
           Context: HasRequirementsToDoSomethingSmart,
       {
           fn do_something(context: &Context, /* ... */) {
               /* ... */
               context.perform_action(/* ... */);
               /* ... */
           }
       }
   }
   ```

   We now has a `CanDoSomething` consumer trait, and a `SomethingDoer`
   provider trait. We then define a `DoSomethingSmart` component that
   implements `SomethingDoer` for any generic `Context`, provided that
   the `Context` provides `CanPerformAction`.

   With that, if a concrete context provides `CanPerformAction`, it can
   also provide `CanDoSomething` by calling `DoSomethingSmart` in its
   implementation for `CanDoSomething`.

   It is worth noting that the transitive dependency
   `HasRequirementsToPerformSimpleAction` is not seen anywhere inside the
   `consumer` module. In other words, the `consumer` module is _decoupled_
   from the requirements of implementing `CanPerformAction`. If the
   concrete context implements `CanPerformAction` by using
   `PerformSimpleAction`, then the constraints are propagated _automatically_
   while completely bypassing the definitions in `consumer`.

    ## All-In-One Traits

    Context-generic programming provides a lot of flexibility for context
    implementations to choose on how to wire up consumer traits with provider
    trait implementations. The late-bound nature of dependency injection
    also means that we do not know the exact requirements the concrete
    context needs to provide until all of the wirings have been decided.

    To make it easy for normal users to use the components, we can provide
    an optional set of _all-in-one_ traits so that users can implement only
    a handful of traits for their concrete contexts, and let the framework
    do the wiring for them. The all-in-one traits provides the convenience of
    less wirings, with the trade off of less customizability.

    One way to think of this is that we can imagine the all-in-one traits
    being like a motherboard of a computer. It provides a fixed number of
    sockets which you can only plug in with compatible components. If you
    want to use a different component like an unsupported CPU, you would
    have to get a different motherboard or build a new motherboard. But that
    doesn't mean you need to rebuild everything from scratch, because you
    can still reuse the other components from the old motherboard, such as
    RAM and storage.

    ## One-For-All Traits

    The _one-for-all_ (OFA) trait is an all-in-one _provider_ trait that
    the concrete context providers can use to implement low-level features.
    The term one-for-all means here:
    _implement this one trait, then all other traits are implemented for you automatically_.

    The one-for-all trait achieve this by gathering all the low-level
    requirements requirements and define them in a single trait. Consider
    our previous examples, we have the `PerformSimpleAction` and `DoSomethingSmart`
    components that can be reused. However in order to use them, the context
    would also have to satisfy the constraints
    `HasRequirementsToPerformSimpleAction` and `HasRequirementsToDoSomethingSmart`.

    If we want to provide an all-in-one framework to implement contexts
    that provides the consumer traits `PerformSimpleAction` and
    `DoSomethingSmart`, it is sufficient that the context provides the
    low level implementations of `HasRequirementsToPerformSimpleAction`
    and `HasRequirementsToDoSomethingSmart`, and then delegate the high-level
    implementations for `PerformSimpleAction` and `DoSomethingSmart`.

    We can do so with the following one-for-all definitions:

    ```
    trait OfaContext {
        fn gather_requirements_to_perform_simple_action();

        fn gather_requirements_to_do_something_smart();
    }

    struct OfaWrapper<Context> {
        context: Context,
    }
    ```

    The trait `OfaContext` defines the abstract methods a concrete context
    needs to implement. The `OfaWrapper` struct is a wrapper struct that
    wraps any `Context` type that implements `OfaContext`. Using the
    methods provided in `OfaContext`, we can now implement `CanPerformAction`
    for any `OfaWrapper<Context>` as follows:

    ```
    # trait HasRequirementsToPerformSimpleAction {}
    # trait CanPerformAction {
    #     fn perform_action(&self, /* ... */);
    # }
    # trait ActionPerformer<Context> {
    #     fn perform_action(context: &Context, /* ... */);
    # }
    # struct PerformSimpleAction;
    # impl<Context> ActionPerformer<Context> for PerformSimpleAction
    # where
    #     Context: HasRequirementsToPerformSimpleAction,
    # {
    #     fn perform_action(context: &Context, /* ... */) {
    #         unimplemented!()
    #     }
    # }
    # trait OfaContext {
    #     fn gather_requirements_to_perform_simple_action();
    #     fn gather_requirements_to_do_something_smart();
    # }
    # struct OfaWrapper<Context> {
    #     context: Context,
    # }
    impl<Context>
        HasRequirementsToPerformSimpleAction
        for OfaWrapper<Context>
    where
        Context: OfaContext,
    { /* ... */ }

    impl<Context> CanPerformAction for OfaWrapper<Context>
    where
        Context: OfaContext,
    {
        fn perform_action(&self, /* ... */) {
            PerformSimpleAction::perform_action(self, /* ... */)
        }
    }
    ```

    We first implement `HasRequirementsToPerformSimpleAction` for
    `OfaWrapper<Context>`, given that if `Context` implements `OfaContext`.
    The implementation can make use of the methods in `OfaContext`,
    such as `gather_requirements_to_perform_simple_action`, to satisfy
    the requirements for `HasRequirementsToPerformSimpleAction`.

    We then implement `CanPerformAction` for `OfaWrapper<Context>`,
    also given that if `Context` implements `OfaContext`. The implementation
    simply delegates the call to `PerformSimpleAction`, and this is allowed
    because the constraint `HasRequirementsToPerformSimpleAction` has already
    been satisfied.

    Similarly, we can implement `CanDoSomething` for `OfaWrapper<Context>`
    following the same convention:

    ```
    # trait HasRequirementsToDoSomethingSmart {}
    # trait CanDoSomething {
    #     fn do_something(&self, /* ... */);
    # }
    # trait SomethingDoer<Context> {
    #     fn do_something(context: &Context, /* ... */);
    # }
    # struct DoSomethingSmart;
    # impl<Context> SomethingDoer<Context> for DoSomethingSmart
    # where
    #     Context: HasRequirementsToDoSomethingSmart,
    # {
    #     fn do_something(context: &Context, /* ... */) {
    #     }
    # }
    # trait OfaContext {
    #     fn gather_requirements_to_perform_simple_action();
    #     fn gather_requirements_to_do_something_smart();
    # }
    # struct OfaWrapper<Context> {
    #     context: Context,
    # }
    impl<Context> HasRequirementsToDoSomethingSmart
        for OfaWrapper<Context>
    where
        Context: OfaContext,
    { /* ... */ }

    impl<Context> CanDoSomething for OfaWrapper<Context>
    where
        Context: OfaContext,
    {
        fn do_something(&self, /* ... */) {
            DoSomethingSmart::do_something(self, /* ... */)
        }
    }
    ```

    With the blanket implementations by `OfaWrapper`, a concrete context like
    `AppContext` now only needs to implement `OfaContext`. It can then
    call methods like `perform_action` and `do_something` by wrapping
    the concrete context into `OfaWrapper<AppContext>`.

    ## All-For-One Traits

    The _all-for-one_ (AFO) trait is an all-in-one _consumer_ trait that
    consumers of a generic context can use to consume all features offered
    by the context. The term all-for-one means here:
    _import all the traits available by importing only this one trait_.

    The all-for-one trait achieve this by specifying all consumer traits
    as its _parent_ trait. With that, when the all-for-one trait is imported
    in the `where` clause, Rust's trait system would help to also automatically
    import all its parent traits and make them available for use.

    Using our previous examples, consider an external consumer that want to
    use both `CanPerformAction` and `CanDoSomething`. They can define a
    context-generic function as follows:

    ```
    # trait CanPerformAction {
    #     fn perform_action(&self, /* ... */);
    # }
    # trait CanDoSomething {
    #     fn do_something(&self, /* ... */);
    # }
    fn run_assembly<Context>(context: Context, /* ... */)
    where
        Context: CanPerformAction + CanDoSomething,
    { /* ... */ }
    ```

    With only two components, it is still manageable to list everything as
    explicit constraints. But as the number of components increase, the
    explicit list can become tedious to repeat.

    We can instead define an all-for-one context as follows:

    ```
    # trait CanPerformAction {
    #     fn perform_action(&self, /* ... */);
    # }
    # trait CanDoSomething {
    #     fn do_something(&self, /* ... */);
    # }
    trait AfoContext: CanPerformAction + CanDoSomething {}
    impl<Context> AfoContext for Context
    where
        Context: CanPerformAction + CanDoSomething,
    {}
    ```

    We define the `AfoContext` with `CanPerformAction` and `CanDoSomething`
    as its parent traits. We then immediately define a blanket implementation
    for `AfoContext` for any generic `Context` type that implements
    `CanPerformAction` and `CanDoSomething`. This means that `AfoContext`
    is automatically implemented for any `Context` type that implements
    `CanPerformAction` and `CanDoSomething`.

    With that, functions that consume any subset of the components can simply
    import `AfoContext` without having to know the detailed traits for
    each API they want to use:

    ```
    # trait AfoContext { }
    fn run_assembly<Context>(context: Context, /* ... */)
    where
        Context: AfoContext,
    { /* ... */ }
    ```

    Note that the all-for-one trait is meant for _external_ consumption.
    This means that any internal components such as `PerformSimpleAction`
    and `DoSomethingSmart` should _not_ use `AfoContext` to import their
    dependencies, as otherwise it would cause cyclic dependencies in the
    implementation graph.

    ## One-For-All and All-For-One

    The main difference between a one-for-all trait and an all-for-one trait
    is that the former is a _provider_ trait to be used by concrete context
    implementers, while the latter is a _consumer_ trait to be used by
    consumers of a generic context.

    There is also a relation between one-for-all and all-for-one, in that
    for any collection of components, an implementation of the one-for-all trait
    for that collection should be sufficient to implement all requirements
    in the all-in-one trait.

    In other words, we can construct a _proof_ that one-for-all implements
    all-for-one:

    ```
    # trait CanPerformAction {
    #     fn perform_action(&self, /* ... */);
    # }
    # trait ActionPerformer<Context> {
    #     fn perform_action(context: &Context, /* ... */);
    # }
    # struct PerformSimpleAction;
    # impl<Context> ActionPerformer<Context> for PerformSimpleAction
    # {
    #     fn perform_action(context: &Context, /* ... */) {
    #         unimplemented!()
    #     }
    # }
    # trait CanDoSomething {
    #     fn do_something(&self, /* ... */);
    # }
    # trait SomethingDoer<Context> {
    #     fn do_something(context: &Context, /* ... */);
    # }
    # struct DoSomethingSmart;
    # impl<Context> SomethingDoer<Context> for DoSomethingSmart
    # {
    #     fn do_something(context: &Context, /* ... */) {
    #     }
    # }
    # trait OfaContext {}
    # struct OfaWrapper<Context> {
    #     context: Context,
    # }
    # impl<Context> CanDoSomething for OfaWrapper<Context>
    # where
    #     Context: OfaContext,
    # {
    #     fn do_something(&self, /* ... */) {
    #         DoSomethingSmart::do_something(self, /* ... */)
    #     }
    # }
    # impl<Context> CanPerformAction for OfaWrapper<Context>
    # where
    #     Context: OfaContext,
    # {
    #     fn perform_action(&self, /* ... */) {
    #         PerformSimpleAction::perform_action(self, /* ... */)
    #     }
    # }
    # trait AfoContext: CanPerformAction + CanDoSomething {}
    # impl<Context> AfoContext for Context
    # where
    #     Context: CanPerformAction + CanDoSomething,
    # {}
    fn ofa_implements_afo<Context>(context: Context) -> impl AfoContext
    where
        Context: OfaContext,
    {
        OfaWrapper { context }
    }
    ```

    In the function `ofa_implements_afo`, it accepts any generic context
    type `Context` that implements `OfaContext`. It then wraps the context
    inside `OfaWrapper` and returns the wrapped context. However the
    return type of the function is `impl AfoContext`, indicating that it
    is an _existential type_ that implements `AfoContext`. But since the
    actual return type is `OfaWrapper<Context>`, Rust would have to
    automatically ensures that `OfaWrapper<Context>` implements `AfoContext`.

    From the `impl` definitions for `OfaWrapper` earlier, we can confirm
    that `OfaWrapper` indeed implements `CanPerformAction` and `CanDoSomething`,
    which in turns satisfies all the requirements for `AfoContext`. Behind
    the scene, Rust also automatically confirm that the requirements are
    satisfied, and thus the proof compiles successfully.

    Proof functions like `ofa_implements_afo` are useful for us to statically
    checks that the relation between our one-for-all trait and our all-for-one
    trait are _sound_. If we were to make a mistake and miss something, such as
    forgetting to implement `HasAdditionalRequirementsToPerformAction`,
    this would result in a compile-time error on the `ofa_implements_afo`.
    This helps us to catch any mistakes early, and fix it before the concrete
    context is used anywhere.

    ## Conclusion

    This concludes the short introduction to context-generic programming.
    With this, you should be able to start understanding the design patterns
    used in the IBC relayer framework.

    To learn more in depth techniques that are used by the relayer framework,
    check out our full tutorial on context-generic programming
    [here](https://informalsystems.github.io/context-generic-programming/).
*/
