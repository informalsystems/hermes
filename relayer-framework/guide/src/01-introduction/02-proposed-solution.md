# Proposed Solution

The relayer framework aims to solve all these problems by separating out each
concern into different components that can be specified independently. Using
dependency injection, each component can independently specify the dependency
it needs from the surrounding context, and composition of components can be
done without knowing the detailed dependency of each component.
