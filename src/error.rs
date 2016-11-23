/// A generic minimal error trait that fits all use cases encountered by libcore.
/// Implement this trait for any error types you wish to use together with readers
/// and writers
pub trait Error {
    /// Call this when your reader cannot provide any more bytes
    fn unexpected_eof(&'static str) -> Self;
    /// Returns true if this error value is just an interruption and
    /// Rereading should succeed at some point
    fn is_interrupted(&self) -> bool;
    /// Emitted when a write fails to write any bytes
    fn write_zero(&'static str) -> Self;
    /// Use this for generic errors
    fn other(&'static str) -> Self;
}

impl Error for ::Void {
    fn unexpected_eof(_: &'static str) -> Self { panic!("don't construct never errors") }
    fn is_interrupted(&self) -> bool { unreachable!() }
    fn write_zero(_: &'static str) -> Self { panic!("don't construct never errors") }
    fn other(_: &'static str) -> Self { panic!("don't construct never errors") }
}

#[cfg(feature = "std")]
#[derive(Debug)]
struct IoError(&'static str);

#[cfg(feature = "std")]
impl ::std::fmt::Display for IoError {
    fn fmt(&self, fmt: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        fmt.write_str(self.0)
    }
}

#[cfg(feature = "std")]
impl ::std::error::Error for IoError {
    fn description(&self) -> &str { self.0 }
}

#[cfg(feature = "std")]
impl Error for ::std::io::Error {
    fn unexpected_eof(s: &'static str) -> Self {
        ::std::io::Error::new(::std::io::ErrorKind::UnexpectedEof, Box::new(IoError(s)))
    }
    fn is_interrupted(&self) -> bool {
        self.kind() == ::std::io::ErrorKind::Interrupted
    }
    fn write_zero(s: &'static str) -> Self {
        ::std::io::Error::new(::std::io::ErrorKind::WriteZero, Box::new(IoError(s)))
    }
    fn other(s: &'static str) -> Self {
        ::std::io::Error::new(::std::io::ErrorKind::Other, Box::new(IoError(s)))
    }
}
