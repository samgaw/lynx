module
public import OwnershipNif.Internal
public import OwnershipNif.RustlerBridge
public section
open Aeneas Aeneas.Std
namespace OwnershipNif.Properties

theorem checked (code : U64) (valid : code ≠ 7#u64) :
    __CHECKED__ code = RustM.ok true := by
  simp [__CHECKED__, Ownership.Properties.run_returns code valid]

theorem checked_panics : __CHECKED__ (7#u64) = RustM.fail .panic := by
  simp [__CHECKED__, Ownership.Properties.run_panics, bind_fail]

theorem scalar (code : U64) : __SCALAR__ code = RustM.ok true := by
  simp [__SCALAR__, Ownership.Properties.scalar_finishes code]
end OwnershipNif.Properties
