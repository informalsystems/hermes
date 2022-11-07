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
       # trait HasRequirementsToPerformAction {}
       # trait ActionPerformer<Context> {
       #     fn perform_action(context: &Context, /* ... */);
       # }
       struct PerformSimpleAction;
       impl<Context> ActionPerformer<Context> for PerformSimpleAction
       where
           Context: HasRequirementsToPerformAction,
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
   as specified in `HasRequirementsToPerformAction`.

   One thing worth noting is that the constraint `HasRequirementsToPerformAction`
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
       # trait HasRequirementsToPerformAction {}
       # trait CanPerformAction {
       #     fn perform_action(&self, /* ... */);
       # }
       # trait ActionPerformer<Context> {
       #     fn perform_action(context: &Context, /* ... */);
       # }
       # struct PerformSimpleAction;
       # impl<Context> ActionPerformer<Context> for PerformSimpleAction
       # where
       #     Context: HasRequirementsToPerformAction,
       # {
       #     fn perform_action(context: &Context, /* ... */) {
       #         unimplemented!()
       #         /* ... */
       #     }
       # }
       pub struct AppContext { /* ... */ }
       impl HasRequirementsToPerformAction for AppContext { /* ... */ }

       impl CanPerformAction for AppContext {
           fn perform_action(&self, /* ... */) {
               PerformSimpleAction::perform_action(self, /* ... */)
           }
       }
   }
   ```

   We first ensure that the concrete type `AppContext` implements the
   requirements that are needed to call `PerformSimpleAction`, such as by
   implementing `HasRequirementsToPerformAction`. We then implement
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
       # trait HasRequirementsToPerformAction {}
       # trait CanPerformAction {
       #     fn perform_action(&self, /* ... */);
       # }
       # trait ActionPerformer<Context> {
       #     fn perform_action(context: &Context, /* ... */);
       # }
       # struct PerformSimpleAction;
       # impl<Context> ActionPerformer<Context> for PerformSimpleAction
       # where
       #     Context: HasRequirementsToPerformAction,
       # {
       #     fn perform_action(context: &Context, /* ... */) {
       #         unimplemented!()
       #         /* ... */
       #     }
       # }
       pub struct AnotherAppContext { /* ... */ }
       # impl HasRequirementsToPerformAction for AnotherAppContext { /* ... */ }
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
   `HasRequirementsToPerformAction` is not seen anywhere inside the
   `consumer` module. In other words, the `consumer` module is _decoupled_
   from the requirements of implementing `CanPerformAction`. If the
   concrete context implements `CanPerformAction` by using
   `PerformSimpleAction`, then the constraints are propagated _automatically_
   while completely bypassing the definitions in `consumer`.

   ## Conclusion

   This concludes the short introduction to context-generic programming.
   With this, you should be able to start understanding the design patterns
   used in the IBC relayer framework.

   To learn more in depth techniques that are used by the relayer framework,
   check out our full tutorial on context-generic programming
   [here](https://informalsystems.github.io/context-generic-programming/).
*/
