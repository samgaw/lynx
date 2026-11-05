//! Reproducer for borrowed enum fields containing a static string.

/// An enum holding a static string.
#[derive(Debug)]
pub enum Borrowed {
    Text(&'static str),
    Empty,
}

/// Return a shorter shared borrow of the referenced value.
pub fn shared<'a, T: ?Sized>(value: &'a &T) -> &'a T {
    value
}

/// Exercise the same nested shared borrow as a derived Display implementation.
pub fn nested(value: &Borrowed) -> bool {
    match value {
        Borrowed::Text(text) => {
            let _borrowed = shared(&text);
            true
        }
        Borrowed::Empty => false,
    }
}

/// Preserve the actual borrowed string through the generic helper.
pub fn extract(value: &Borrowed) -> Option<&'static str> {
    match value {
        Borrowed::Text(text) => Some(*shared(&text)),
        Borrowed::Empty => None,
    }
}
