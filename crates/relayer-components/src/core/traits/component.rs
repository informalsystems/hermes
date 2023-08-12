use crate::core::traits::sync::Async;

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

#[macro_export]
macro_rules! forward_components {
    ( $target:ident $( < $( $param:ident ),* $(,)? > )?, $forwarded:ty $(,)?, [$(,)?] ) => {

    };
    ( $target:ident $( < $( $param:ident ),* $(,)? > )?, $forwarded:ty $(,)?, [$name:ty, $($rest:tt)*]  ) => {
        $crate::forward_component!($name, $target $( < $( $param ),* > )*, $forwarded);
        $crate::forward_components!($target $( < $( $param ),* > )*, $forwarded, [ $($rest)* ]);
    };
}
