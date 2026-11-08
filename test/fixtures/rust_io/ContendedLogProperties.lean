module
public import Record.RegisteredLogProperties
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.ContendedLogProperties
open NativeFile Record.Properties Record.CrashProperties Record.FramedLogProperties Record.LockedProperties
  Record.SharedLogProperties Record.NativeLogProperties Record.OverlappingLogProperties

attribute [local simp] NativeCodec.typeName NativeCodec.encode NativeResourceArc.typeName
  NativeResourceArc.handleType NativeResourceArc.termType NativeMutex.typeName NativeFile.typeName

@[expose] def beforeCounter (first : Bool) : Nat := if first then 6 else 8
@[expose] def beforeFrame (first : Bool) := if first then pinnedFrame else decodedFrame
@[expose] def decodedOwners (first : Bool) := if first then decodedFrame else overlappingFrame
@[expose] def beforeCount (first : Bool) : Nat := if first then 1 else 2
@[expose] def resource (first : Bool) : NativeResourceArc shared_log.LogResource :=
  ⟨3, beforeCounter first + 1⟩

/-- The real continuation at the lock wait, including the native exception and
result adapter. The poll itself has not executed. -/
@[expose] def resume (first : Bool) (value : U16) :
    Except Exception (core.result.Result (NativeGuard NativeFile)
      (NativePoisonError (NativeGuard NativeFile))) → Result Term := fun reply =>
  Rustler.executeNative (do
    let acquired ← Result.ofExcept reply
    afterGuard (resource first) (recoverGuard acquired) value) Rustler.encodeBool

theorem resume_wait (first : Bool) (value : U16) :
    Rustler.executeNative (do
      let acquired ← NativeMutex.lock (⟨1⟩ : NativeMutex NativeFile)
      afterGuard (resource first) (recoverGuard acquired) value) Rustler.encodeBool =
      .wait (NativeMutex.pollLock (⟨1⟩ : NativeMutex NativeFile)) (resume first value) := by
  rw [NativeMutex.lock, Result.wait_bind, Rustler.executeNative_wait]
  congr 1
  funext reply
  cases reply <;> rfl

/-- Actual resource decode and borrow end at the mutex wait. In the peer case,
that decoder runs while the other owner's guard is still held. -/
theorem decoded_lock_prefix (pid : PID) (first : Bool) (types : List String)
    (registered : NativeResourceArc.typeName shared_log.LogResource ∈ types)
    (contents : Term) (state : State) (value : U16) :
    Result.RegisteredPrefix pid (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      Rustler.executeNative (__APPEND__ owner value) Rustler.encodeBool)
      (Record.ScheduledLogProperties.shared (beforeCounter first) (beforeFrame first) contents state) types
      (.wait (NativeMutex.pollLock (⟨1⟩ : NativeMutex NativeFile)) (resume first value))
      (Record.ScheduledLogProperties.shared (beforeCounter first + 1) (decodedOwners first) contents state) types := by
  have decoded := NativeResourceArc.decode_live_registeredPrefix pid
    (⟨3,5⟩ : NativeResourceArc shared_log.LogResource) 6 logPayload (beforeCount first)
    (Record.ScheduledLogProperties.shared (beforeCounter first) (beforeFrame first) contents state) types
    registered
    (by cases first <;> decide) (by cases first <;> decide)
    (by cases first <;> simp [Record.ScheduledLogProperties.shared, beforeFrame, decodedFrame, pinnedFrame,
      NativeResourceArc.vmCells])
    (by cases first <;> simp [Record.ScheduledLogProperties.shared, beforeFrame, decodedFrame, pinnedFrame,
      NativeResourceArc.vmCells])
    (by cases first <;> simp [Record.ScheduledLogProperties.shared, beforeFrame, beforeCount, decodedFrame,
      pinnedFrame, NativeResourceArc.vmCells])
    (by cases first <;> simp [Record.ScheduledLogProperties.shared, beforeFrame, beforeCount, decodedFrame,
      pinnedFrame, NativeResourceArc.vmCells])
    (by cases first <;> simp [Record.ScheduledLogProperties.shared, beforeFrame, beforeCounter, decodedFrame,
      pinnedFrame, NativeResourceArc.vmCells])
  have borrowed := NativeResourceArc.deref_live_registeredPrefix pid (resource first) logPayload
    (beforeCount first + 1)
    (Record.ScheduledLogProperties.shared (beforeCounter first + 1) (decodedOwners first) contents state) types
    (by cases first <;> decide) (by cases first <;> decide)
    (by cases first <;> simp [Record.ScheduledLogProperties.shared, resource, beforeCounter, decodedOwners,
      overlappingFrame, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    (by cases first <;> simp [Record.ScheduledLogProperties.shared, resource, beforeCounter, decodedOwners,
      beforeCount, overlappingFrame, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    (by cases first <;> simp [Record.ScheduledLogProperties.shared, resource, beforeCounter, decodedOwners,
      beforeCount, overlappingFrame, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
  have native : Result.RegisteredPrefix pid (__APPEND__ (resource first) value)
      (Record.ScheduledLogProperties.shared (beforeCounter first + 1) (decodedOwners first) contents state) types
      (do let acquired ← NativeMutex.lock (⟨1⟩ : NativeMutex NativeFile)
          afterGuard (resource first) (recoverGuard acquired) value)
      (Record.ScheduledLogProperties.shared (beforeCounter first + 1) (decodedOwners first) contents state) types := by
    rw [caller_contract]
    simpa only [Result.ok_bind, logPayload] using borrowed.bind
      (fun log => do let acquired ← NativeMutex.lock log.file
                     afterGuard (resource first) (recoverGuard acquired) value)
  have encoded := Rustler.executeNative_registeredPrefix native Rustler.encodeBool
  rw [resume_wait] at encoded
  have head := decoded.bind (fun owner => Rustler.executeNative (__APPEND__ owner value) Rustler.encodeBool)
  cases first <;>
    simp only [beforeCounter, beforeFrame, decodedOwners, beforeCount, Bool.false_eq_true,
      ↓reduceIte, Result.ok_bind] at head encoded ⊢
  all_goals
    apply head.trans
    simpa [resource, beforeCounter, Record.ScheduledLogProperties.shared, overlappingFrame, decodedFrame,
      pinnedFrame, NativeResourceArc.vmCells, logPayload] using encoded

end Record.ContendedLogProperties
