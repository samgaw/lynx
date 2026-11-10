//! Owned values with observable destruction.
/// A value whose destructor validates its code.
#[derive(Debug)]
pub struct Audit {
    /// Code checked at destruction.
    pub code: u64,
}
impl Drop for Audit {
    fn drop(&mut self) {
        assert!(self.code != 7);
    }
}
/// Consumes a value and executes its destructor.
///
/// # Panics
/// Propagates a panic from the value's destructor.
pub fn consume<T>(_value: T) {}

/// A scope guard that updates the original borrowed flag at destruction.
#[derive(Debug)]
pub struct Flip<'a>(pub &'a mut bool);

impl Drop for Flip<'_> {
    fn drop(&mut self) {
        *self.0 = !*self.0;
    }
}

/// Flips the borrowed flag by executing the guard's actual destructor.
pub fn flip(value: &mut bool) {
    let _guard = Flip(value);
}

/// Flips the borrowed flag on both normal exit and panic.
///
/// # Panics
/// Panics when `accepted` is false, running the guard's destructor.
pub fn checked_flip(value: &mut bool, accepted: bool) {
    let _guard = Flip(value);
    assert!(accepted);
}

/// Mutates protected contents before checking the request.
///
/// # Panics
/// Panics after mutation when the request is rejected.
pub fn mutate_before_check(value: &mut bool, accepted: bool) {
    *value = !*value;
    assert!(accepted);
}

/// Toggles a borrowed flag without panicking.
pub fn toggle(value: &mut bool) {
    *value = !*value;
}
