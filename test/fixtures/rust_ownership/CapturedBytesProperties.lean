module
public import CapturedBytes.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx ownership_app
namespace CapturedBytes.Properties

theorem take_bytes (input : alloc.vec.Vec U8) (accepted : Bool) :
    ownership_base.take_bytes input accepted = NativeM.ok
      ((if accepted then .Ok (.Ok (some input)) else .Err ()), alloc.vec.Vec.new U8) := by
  cases accepted <;> simp [ownership_base.take_bytes, ownership_base.require_bytes,
    core.mem.replace, NativeM.ok]

theorem checked_bytes (input : alloc.vec.Vec U8) (accepted : Bool) :
    ownership_app.checked_bytes input accepted = NativeM.ok
      ((if accepted then .Ok (.Ok (some input)) else .Err ()), alloc.vec.Vec.new U8) := by
  cases accepted <;> simp [ownership_app.checked_bytes, take_bytes, ownership_base.require_bytes, NativeM.ok]

end CapturedBytes.Properties
