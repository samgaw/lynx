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
