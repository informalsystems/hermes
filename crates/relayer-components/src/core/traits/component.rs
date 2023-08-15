use crate::core::traits::sync::Async;

pub trait DelegateComponent<Name>: Async {
    type Delegate;
}

#[macro_export]
macro_rules! delegate_component {
    ( $key:ty, $target:ident $( < $( $param:ident ),* $(,)? > )?, $forwarded:ty $(,)?  ) => {
        impl< $( $( $param ),* )* >
            $crate::core::traits::component::DelegateComponent<$key>
            for $target $( < $( $param ),* > )*
        where
            Self: $crate::core::traits::sync::Async,
        {
            type Delegate = $forwarded;
        }
    };
}

#[macro_export]
macro_rules! delegate_components {
    ( [$(,)?], $target:ident $( < $( $param:ident ),* $(,)? > )?, $forwarded:ty $(,)? ) => {

    };
    ( [$name:ty, $($rest:tt)*], $target:ident $( < $( $param:ident ),* $(,)? > )?, $forwarded:ty $(,)?  ) => {
        $crate::delegate_component!($name, $target $( < $( $param ),* > )*, $forwarded);
        $crate::delegate_components!([ $($rest)* ], $target $( < $( $param ),* > )*, $forwarded);
    };
}
