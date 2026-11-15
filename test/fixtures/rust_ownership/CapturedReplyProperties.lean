module
public import CapturedReplies.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx ownership_app
namespace CapturedReplies.Properties
abbrev Reply := core.result.Result (Option Bool) U8
abbrev CapturedReply := core.result.Result Reply Unit
@[expose] def response (value present rejected : Bool) : Reply :=
  if rejected then .Err 7#u8 else if present then .Ok (some (!value)) else .Ok none
@[expose] def captured (value accepted present rejected : Bool) : CapturedReply :=
  if accepted then .Ok (response value present rejected) else .Err ()

theorem reply (value accepted present rejected : Bool) :
    ownership_base.reply value accepted present rejected =
      NativeM.ok (captured value accepted present rejected, !value) := by
  cases accepted <;> cases present <;> cases rejected <;>
    simp [ownership_base.reply, captured, response, NativeM.ok]

theorem checked_reply (value accepted present rejected : Bool) :
    ownership_app.checked_reply value accepted present rejected =
      NativeM.ok (captured value accepted present rejected, !value) := by
  cases accepted <;> simp [ownership_app.checked_reply, reply, captured, NativeM.ok]

theorem guard_composes (guard : NativeGuard Bool) (accepted present rejected : Bool) :
    ownership_app.guard_reply guard accepted present rejected = (do
      let updated := {guard with value := !guard.value}
      if accepted then
        NativeGuard.release updated
        NativeM.ok (captured guard.value accepted present rejected)
      else
        NativeGuard.releasePanicking updated
        NativeM.ok (.Err ())) := by
  cases accepted <;>
    simp [ownership_app.guard_reply, reply, captured, NativeGuard.deref_mut, NativeM.lift,
      NativeM.ok, NativeDrop.drop, NativeUnwindDrop.drop]

theorem guard_heap (guard : NativeGuard Bool) (accepted present rejected poisoned original : Bool)
    (env : Environment) (owner : guard.ownerContext = env.currentPid)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == guard.mutex.id) =
      [(guard.mutex.id, NativeMutex.typeName Bool,
        NativeMutex.lockedContents guard.ownerContext guard.token poisoned original)]) :
    ownership_app.guard_reply guard accepted present rejected env =
      (.ok (captured guard.value accepted present rejected),
       {env with nativeHeap := env.nativeHeap.map fun cell =>
         if cell.1 == guard.mutex.id then
           (guard.mutex.id, NativeMutex.typeName Bool,
            .tuple #[.atom "unlocked", .atom (if poisoned || !accepted then "poisoned" else "unpoisoned"),
              NativeCodec.encode (!guard.value)])
         else cell}) := by
  rw [guard_composes]
  cases accepted
  · simpa [NativeM.ok, captured] using
      (NativeGuard.releasePanicking_owned_next {guard with value := !guard.value}
        original poisoned (NativeM.ok (.Err ()) : NativeM CapturedReply) env owner stored)
  · simpa [NativeM.ok, captured] using
      (NativeGuard.release_owned_next {guard with value := !guard.value}
        original poisoned (NativeM.ok (.Ok (response guard.value present rejected)) : NativeM CapturedReply)
        env owner stored)
end CapturedReplies.Properties
