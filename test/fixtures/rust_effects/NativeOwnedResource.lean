module
public import Resource.Critical
public section
open Aeneas Aeneas.Std effects_native Lynx
namespace Resource.Properties

@[expose] def initial (env : Environment) : Environment :=
  {env with refCounter := 0, nativeHeap := []}

@[expose] def cell (value : U64) : Nat × String × Term :=
  (1, NativeMutex.typeName effects_core.Counter,
    .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode ({value} : effects_core.Counter)])

@[expose] def live (env : Environment) (value : U64) (token : Nat := 3) (counter : Nat := 3) : Environment :=
  {env with refCounter := counter, nativeHeap := [
    (token, NativeResourceArc.handleType CounterResource, .reference 2),
    (2, NativeResourceArc.typeName CounterResource,
      .tuple #[.integer 1, NativeCodec.encode ({state := ⟨1⟩} : CounterResource)]), cell value]}

@[expose] def payloadReclaimed (env : Environment) (token : Nat := 3) (counter : Nat := 3) : Environment :=
  {env with refCounter := counter, nativeHeap := [
    (token, NativeResourceArc.handleType CounterResource, .reference 2),
    (2, NativeResourceArc.typeName CounterResource,
      .tuple #[.integer 1, NativeCodec.encode ({state := ⟨1⟩} : CounterResource)])]}

theorem construct_next {α : Type} (value : U64) (env : Environment)
    (next : NativeResourceArc CounterResource → NativeM α)
    (registered : NativeResourceArc.typeName CounterResource ∈ env.nativeResourceTypes) :
    (resource_new value >>= next) (initial env) = next ⟨2,3⟩ (live env value) := by
  simp [resource_new, NativeMutex.new, NativeResourceArc.newOwned, NativeResourceArc.new,
    NativeM.allocate, NativeM.ok, initial, live, cell, registered, bind_assoc]

theorem construct (value : U64) (env : Environment)
    (registered : NativeResourceArc.typeName CounterResource ∈ env.nativeResourceTypes) :
    resource_new value (initial env) = (.ok ⟨2,3⟩, live env value) := by
  simp [resource_new, NativeMutex.new, NativeResourceArc.newOwned, NativeResourceArc.new,
    NativeM.allocate, NativeM.ok, initial, live, cell, registered]

theorem unregistered_cleanup (value : U64) (env : Environment)
    (absent : NativeResourceArc.typeName CounterResource ∉ env.nativeResourceTypes) :
    resource_new value (initial env) =
      (.error (.error (.atom "rust_panicked")), {env with refCounter := 1, nativeHeap := []}) := by
  simp [resource_new, NativeMutex.new, NativeResourceArc.newOwned, NativeResourceCleanup.cleanup,
    CounterResource.drop_owned, NativeOwnedDrop.drop, NativeMutex.dispose,
    NativeM.allocate, NativeM.readCell, NativeM.removeCell, NativeM.ok, NativeM.fail,
    initial, absent, NativeCodec.roundtrip]

theorem payload_cleanup_next {α : Type} (value : U64) (env : Environment) (token counter : Nat) (valid : 3 ≤ token) (next : NativeM α) :
    (do CounterResource.drop_owned ⟨⟨1⟩⟩; next) (live env value token counter) = next (payloadReclaimed env token counter) := by
  have n1 : (token == 1) = false := by simp; omega
  have n2 : (token == 2) = false := by simp; omega
  simp [bne_eq, n1, n2, List.filter, CounterResource.drop_owned, NativeOwnedDrop.drop, NativeMutex.dispose,
    NativeM.readCell, NativeM.removeCell, NativeM.ok, live, cell, payloadReclaimed, (by omega : token ≠ 1),
    NativeMutex.typeName, NativeResourceArc.typeName, NativeResourceArc.handleType, NativeCodec.roundtrip]

theorem final_release_next {α : Type} (next : Unit → NativeM α) (value : U64) (env : Environment) (token counter : Nat) (valid : 3 ≤ token) :
    (resource_release ⟨2,token⟩ >>= next) (live env value token counter) =
      next () {env with refCounter := counter, nativeHeap := []} := by
  have n1 : (token == 1) = false := by simp; omega
  have n2 : (token == 2) = false := by simp; omega
  have r1 : (1 == token) = false := by simp; omega
  have r2 : (2 == token) = false := by simp; omega
  have cleaned : ∀ next : NativeM α,
      (do NativeResourceCleanup.cleanup ({state := ⟨1⟩} : CounterResource); next) (live env value token counter) =
        next (payloadReclaimed env token counter) := payload_cleanup_next value env token counter valid
  have released := NativeResourceArc.releaseOwned_last_run_next
    (⟨2,token⟩ : NativeResourceArc CounterResource) ⟨⟨1⟩⟩ next (live env value token counter) (payloadReclaimed env token counter)
    (by simp [List.filter, live, cell, (by omega : token ≠ 1), (by omega : token ≠ 2), n1, n2, r1, r2, bne_eq]) (by simp [List.filter, live, cell, (by omega : token ≠ 1), (by omega : token ≠ 2), n1, n2, r1, r2, bne_eq])
    (by simp [n1, n2, r1, r2, bne_eq, List.filter, live, cell, NativeMutex.typeName, NativeResourceArc.typeName, NativeResourceArc.handleType, (by omega : token ≠ 2)]) cleaned
    (by simp [List.filter, payloadReclaimed, (by omega : token ≠ 2), n1, n2, r1, r2, bne_eq]) (by simp [List.filter, payloadReclaimed, (by omega : token ≠ 2), n1, n2, r1, r2, bne_eq])
    (by simp [n1, n2, r1, r2, bne_eq, List.filter, payloadReclaimed, NativeMutex.typeName, NativeResourceArc.typeName, NativeResourceArc.handleType, (by omega : token ≠ 2)])
  simpa [n1, n2, r1, r2, bne_eq, List.filter, resource_release, NativeOwnedDrop.drop, payloadReclaimed, (by omega : token ≠ 2)] using released

@[expose] def aliased (env : Environment) (value : U64) : Environment :=
  {env with refCounter := 4, nativeHeap := [
    (4, NativeResourceArc.handleType CounterResource, .reference 2),
    (3, NativeResourceArc.handleType CounterResource, .reference 2),
    (2, NativeResourceArc.typeName CounterResource,
      .tuple #[.integer 2, NativeCodec.encode ({state := ⟨1⟩} : CounterResource)]), cell value]}

theorem clone_next {α : Type} (value : U64) (env : Environment)
    (next : NativeResourceArc CounterResource → NativeM α) :
    (resource_clone ⟨2,3⟩ >>= next) (live env value) = next ⟨2,4⟩ (aliased env value) := by
  have cloned := NativeResourceArc.clone_single_next
    (⟨2,3⟩ : NativeResourceArc CounterResource) ⟨⟨1⟩⟩ next (live env value)
    (by simp [live, cell]) (by simp [live, cell])
    (by simp [bne_eq, List.filter, live, cell, NativeMutex.typeName, NativeResourceArc.typeName, NativeResourceArc.handleType])
    (by simp [live, cell])
  simpa [List.filter, List.map, resource_clone, live, aliased, cell, NativeM.ok] using cloned

theorem nonfinal_release_next {α : Type} (value : U64) (env : Environment)
    (next : Unit → NativeM α) :
    (resource_release ⟨2,3⟩ >>= next) (aliased env value) = next () (live env value 4 4) := by
  have released := NativeResourceArc.releaseOwned_retained_run_next
    (⟨2,3⟩ : NativeResourceArc CounterResource) ⟨⟨1⟩⟩ next (aliased env value)
    (by simp [aliased, cell]) (by simp [aliased, cell])
    (by simp [aliased, cell, NativeMutex.typeName, NativeResourceArc.typeName, NativeResourceArc.handleType])
  simpa [List.filter, List.map, resource_release, NativeOwnedDrop.drop, live, aliased, cell] using released

theorem update_next {α : Type} (value amount : U64) (env : Environment)
    (next : Bool → NativeM α) :
    ∃ changed updated,
      (resource_locked_increment ⟨2,4⟩ amount >>= next) (live env value 4 4) =
        next changed (live env updated 4 5) ∧
      (if changed then updated.val = value.val + amount.val
       else updated = value ∧ U64.max < value.val + amount.val) := by
  obtain ⟨changed, updated, computed, arithmetic⟩ := Resource.Critical.critical_state_next
    next (⟨1⟩ : NativeMutex effects_core.Counter) ⟨value⟩ amount false (live env value 4 4)
    (by simp [List.filter, live, cell]) (by simp [live, cell])
  refine ⟨changed, updated.value, ?_, ?_⟩
  · have observed := NativeResourceArc.deref_single_next
      (⟨2,4⟩ : NativeResourceArc CounterResource) ⟨⟨1⟩⟩
      (fun payload => effects_core.locked_increment payload.state amount >>= next) (live env value 4 4)
      (by simp [List.filter, live, cell]) (by simp [List.filter, live, cell])
      (by simp [List.filter, live, cell, NativeMutex.typeName,
        NativeResourceArc.typeName, NativeResourceArc.handleType])
    simp only [resource_locked_increment, monadLift_self, bind_assoc]
    rw [observed]
    cases updated
    simpa [live, cell, List.map] using computed
  · cases changed <;> cases updated <;> simpa using arithmetic

theorem complete_cycle (value amount : U64) (env : Environment)
    (registered : NativeResourceArc.typeName CounterResource ∈ env.nativeResourceTypes) :
    ∃ (changed : Bool) (updated : U64),
      resource_cycle value amount (initial env) =
        (.ok changed, {env with refCounter := 5, nativeHeap := []}) ∧
      (if changed then updated.val = value.val + amount.val
       else updated = value ∧ U64.max < value.val + amount.val) := by
  let finish : Bool → NativeM Bool := fun changed => do
    resource_release ⟨2,4⟩
    NativeM.ok changed
  obtain ⟨changed, updated, computed, arithmetic⟩ := update_next value amount env finish
  refine ⟨changed, updated, ?_, arithmetic⟩
  simp only [resource_cycle, monadLift_self, bind_assoc]
  rw [construct_next value env _ registered]
  rw [clone_next value env]
  rw [nonfinal_release_next value env]
  change (resource_locked_increment ⟨2,4⟩ amount >>= finish) (live env value 4 4) = _
  rw [computed]
  simpa [finish, NativeM.ok] using
    final_release_next (fun _ => NativeM.ok changed) updated env 4 5 (by decide)

end Resource.Properties
