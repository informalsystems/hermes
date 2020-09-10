#[macro_export]
macro_rules! downcast {
    ( $e1:expr => $p1:path, $( $e:expr => $p:path ),+ $(,)? ) => {
        downcast!($e1 => $p1).zip(downcast!($($e => $p),+))
    };

    ($e:expr => $p:path) => {
        match $e {
            $p(e) => Some(e),
            #[allow(unreachable_patterns)]
            _ => None,
        }
    };

    () => {
        None
    }
}