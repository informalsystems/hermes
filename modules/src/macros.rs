/// Downcast the given arguments to the associated enum variant.
///
/// ## Note
/// Only works for enums whose variants only hold a single value.
///
/// ## Example
///
/// ```rust
/// use ibc::downcast;
///
/// enum Foo {
///     Bar(u32),
///     Baz(bool),
/// }
///
/// let bar = Foo::Bar(42);
/// let baz = Foo::Baz(true);
///
/// if let Some(value) = downcast!(bar => Foo::Bar) {
///     println!("value is a u32: {}", value);
/// }
///
/// if let Some(value) = downcast!(baz => Foo::Baz) {
///     println!("value is a bool: {}", value);
/// }
///
/// if let Some((a, b)) = downcast!(bar => Foo::Bar, baz => Foo::Baz) {
///     println!("a is a u32: {}", a);
///     println!("b is a bool: {}", b);
/// }
/// ```
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
