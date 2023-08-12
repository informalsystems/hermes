use crate::core::traits::sync::Async;

pub trait HasComponents: Async {
    type Components: Async;
}

pub trait HasComponent<Name>: Async {
    type Component;
}

#[macro_export]
macro_rules! forward_component {
    ( $key:ty, $target:ident $( < $( $param:ident ),* $(,)? > )?, $forwarded:ty $(,)?  ) => {
        impl< $( $( $param ),* )* >
            $crate::core::traits::component::HasComponent<$key>
            for $target $( < $( $param ),* > )*
        where
            Self: $crate::core::traits::sync::Async,
        {
            type Component = $forwarded;
        }
    };
}
