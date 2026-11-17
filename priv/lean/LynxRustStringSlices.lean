module
public import __PREFIX__.StringViewsModel
public section
open Aeneas Aeneas.Std
namespace __PREFIX__.StringSlices

@[expose] def get {I Output : Type}
    (inst : core.slice.index.SliceIndex I Str Output) (text : Str) (index : I) :
    RustM (Option Output) := inst.get index text

@[expose] def rangeGet (range : core.ops.range.Range Usize) (text : Str) :
    RustM (Option Str) :=
  if __PREFIX__.StringViews.isCharBoundary text range.start &&
      __PREFIX__.StringViews.isCharBoundary text range.end then
    core.slice.index.SliceIndexRangeUsizeSlice.get range text
  else .ok none

@[expose] def fromGet (range : core.ops.range.RangeFrom Usize) (text : Str) :
    RustM (Option Str) := rangeGet ⟨range.start, Slice.len text⟩ text

@[expose] def toGet (range : core.ops.range.RangeTo Usize) (text : Str) :
    RustM (Option Str) := rangeGet ⟨0#usize, range.end⟩ text

-- Unsupported dictionary slots exhaust verification. They are not native
-- outcomes and cannot establish successful execution of an unchecked operation.
@[expose] def RangeIndex : core.slice.index.SliceIndex (core.ops.range.Range Usize) Str Str := {
  get := rangeGet
  get_mut := fun _ _ => .fail .undef
  get_unchecked := fun _ _ => .fail .undef
  get_unchecked_mut := fun _ _ => .fail .undef
  index := fun _ _ => .fail .undef
  index_mut := fun _ _ => .fail .undef
}
@[expose] def RangeFromIndex : core.slice.index.SliceIndex (core.ops.range.RangeFrom Usize) Str Str := {
  get := fromGet
  get_mut := fun _ _ => .fail .undef
  get_unchecked := fun _ _ => .fail .undef
  get_unchecked_mut := fun _ _ => .fail .undef
  index := fun _ _ => .fail .undef
  index_mut := fun _ _ => .fail .undef
}
@[expose] def RangeToIndex : core.slice.index.SliceIndex (core.ops.range.RangeTo Usize) Str Str := {
  get := toGet
  get_mut := fun _ _ => .fail .undef
  get_unchecked := fun _ _ => .fail .undef
  get_unchecked_mut := fun _ _ => .fail .undef
  index := fun _ _ => .fail .undef
  index_mut := fun _ _ => .fail .undef
}
end __PREFIX__.StringSlices
