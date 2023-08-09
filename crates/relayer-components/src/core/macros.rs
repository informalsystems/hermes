#[macro_export]
macro_rules! define_component_deriver {
    (   $d:tt,
        $name:ident,
        $trait:path,
        < $( $trait_param:ty ),+ >
        $( where $( $where_type:ty : $bound:ty ),* , )?
        {
            $method:ident ( $( $arg:ident : $arg_type:ty ),* $(,)?  ) -> $ret:ty ;
        }
    ) => {
        #[macro_export]
        macro_rules! $name {
            ( $target:ident $d ( < $d( $param:ident ),* $d(,)? > )?, $source:ty $d(,)?  ) => {
                #[$crate::vendor::async_trait::async_trait]
                impl< $( $trait_param ),* , $d( $d( $param ),* )*>
                    $trait < $( $trait_param ),* >
                    for $target $d( < $d( $param ),* > )*
                where
                    $source: $trait < $( $trait_param ),* >,
                    $target $d( < $d( $param ),* > )*: $crate::core::traits::sync::Async,
                    $d( $d where_type : $d( $d bound )+* ),*
                {
                    async fn $method ( $( $arg: $arg_type ),* ) -> $ret {
                        <$source as $trait < $( $trait_param ),* >
                            :: $method ( $( $arg ),* ).await
                    }
                }
            };
        }
    };
}
