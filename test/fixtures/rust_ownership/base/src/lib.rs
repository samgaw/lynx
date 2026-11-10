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
