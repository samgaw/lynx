module
public import Returned.Properties
public section
open Aeneas Aeneas.Std Lynx ownership_nif
namespace Returned.Framed

private theorem references (left right : Nat) :
    (Term.nativeReference left == Term.nativeReference right) = (left == right) := by
  apply Bool.eq_iff_iff.mpr
  rw [Term.beq_iff_compare_eq, Term.compare_eq_reference]
  simp

private theorem offsets (counter left right : Nat) :
    (counter + left == counter + right) = (left == right) := by
  apply Bool.eq_iff_iff.mpr
  simp

@[expose] def returned (env : Environment) (value : Bool) : Environment :=
  {env with nativeRefCounter := env.nativeRefCounter + 4, nativeHeap :=
    (env.nativeRefCounter + 4, NativeResourceArc.handleType UnwindResource,
      .nativeReference (env.nativeRefCounter + 3)) ::
    (env.nativeRefCounter + 3, NativeResourceArc.typeName UnwindResource,
      .tuple #[.integer 1, NativeCodec.encode ({value := !value} : UnwindResource)]) :: env.nativeHeap}

set_option maxHeartbeats 1000000 in
theorem allocate_next {β : Type} (env : Environment) (value accepted : Bool)
    (registered : NativeResourceArc.typeName UnwindResource ∈ env.nativeResourceTypes)
    (frame : NativeResourceArc.FrameBelow UnwindResource env.nativeRefCounter env.nativeHeap)
    (next : core.result.Result (NativeResourceArc UnwindResource) Unit → NativeM β) :
    (allocate_resource value accepted >>= next) env =
      if accepted then
        next (.Ok ⟨env.nativeRefCounter + 3, env.nativeRefCounter + 4⟩) (returned env value)
      else next (.Err ()) {env with nativeRefCounter := env.nativeRefCounter + 2} := by
  have reg := registered
  simp [NativeResourceArc.typeName] at reg
  have ids1 := frame.cell_absent (id := env.nativeRefCounter + 1) (by omega)
  have ids2 := frame.cell_absent (id := env.nativeRefCounter + 2) (by omega)
  have anys1 := frame.key_unused (id := env.nativeRefCounter + 1) (by omega)
  have anys2 := frame.key_unused (id := env.nativeRefCounter + 2) (by omega)
  have anys3 := frame.key_unused (id := env.nativeRefCounter + 3) (by omega)
  have anys4 := frame.key_unused (id := env.nativeRefCounter + 4) (by omega)
  have removes1 := frame.erase_fresh (id := env.nativeRefCounter + 1) (by omega)
  have removes2 := frame.erase_fresh (id := env.nativeRefCounter + 2) (by omega)
  have tokens := frame.ownership_absent (id := env.nativeRefCounter + 1) (by omega)
  dsimp [NativeResourceArc.handleType] at tokens
  simp only [bne] at removes1 removes2
  cases accepted <;> simp [Returned.Properties.allocate, returned, NativeResourceArc.newCaptured,
    NativeM.capturePanic, NativeResourceArc.new, NativeResourceArc.deref,
    NativeResourceArc.release, NativeResourceArc.takeOwner, NativeResourceArc.ownerState,
    NativeResourceArc.retiredState, NativeResourceArc.ownership, NativeResourceArc.handleType,
    NativeResourceArc.typeName, NativeResourceArc.referenceLimit, NativeCodec.roundtrip,
    NativeM.allocate, NativeM.ok, NativeM.fail, Result.handle, reg, List.filter, references,
    bne, Nat.add_assoc, offsets, ids1, ids2, anys1, anys2, anys3, anys4, removes1, removes2, tokens]


theorem returned_frame (env : Environment) (value : Bool)
    (frame : NativeResourceArc.FrameBelow UnwindResource env.nativeRefCounter env.nativeHeap) :
    NativeResourceArc.FrameBelow UnwindResource (returned env value).nativeRefCounter
      (returned env value).nativeHeap := by
  have prior := frame.mono (upper := env.nativeRefCounter + 4) (by omega)
  intro cell member
  simp only [returned, List.mem_cons] at member
  rcases member with rfl | rfl | member
  · simp [returned, NativeResourceArc.handleType, NativeResourceArc.typeName, NativeResourceArc.termType]
  · simp [returned, NativeResourceArc.handleType, NativeResourceArc.typeName, NativeResourceArc.termType]
  · exact prior cell member

set_option maxHeartbeats 1000000 in
theorem allocate_twice (env : Environment) (left right : Bool)
    (registered : NativeResourceArc.typeName UnwindResource ∈ env.nativeResourceTypes)
    (frame : NativeResourceArc.FrameBelow UnwindResource env.nativeRefCounter env.nativeHeap) :
    (do
      let first ← allocate_resource left true
      let second ← allocate_resource right true
      NativeM.ok (first, second)) env =
    (.ok (.Ok ⟨env.nativeRefCounter + 3, env.nativeRefCounter + 4⟩,
          .Ok ⟨env.nativeRefCounter + 7, env.nativeRefCounter + 8⟩),
      returned (returned env left) right) := by
  rw [allocate_next env left true registered frame]
  simp only [Bool.true_eq, ite_true]
  let first : core.result.Result (NativeResourceArc UnwindResource) Unit :=
    .Ok ⟨env.nativeRefCounter + 3, env.nativeRefCounter + 4⟩
  simpa [first, NativeM.ok, returned, Nat.add_assoc] using
    allocate_next (returned env left) right true registered (returned_frame env left frame)
      (fun second => NativeM.ok (first, second))

set_option maxHeartbeats 1000000 in
theorem rejected_after_return (env : Environment) (left right : Bool)
    (registered : NativeResourceArc.typeName UnwindResource ∈ env.nativeResourceTypes)
    (frame : NativeResourceArc.FrameBelow UnwindResource env.nativeRefCounter env.nativeHeap) :
    (do
      let first ← allocate_resource left true
      let second ← allocate_resource right false
      NativeM.ok (first, second)) env =
    (.ok (.Ok ⟨env.nativeRefCounter + 3, env.nativeRefCounter + 4⟩, .Err ()),
      {returned env left with nativeRefCounter := env.nativeRefCounter + 6}) := by
  rw [allocate_next env left true registered frame]
  simp only [Bool.true_eq, ite_true]
  let first : core.result.Result (NativeResourceArc UnwindResource) Unit :=
    .Ok ⟨env.nativeRefCounter + 3, env.nativeRefCounter + 4⟩
  simpa [first, NativeM.ok, returned, Nat.add_assoc] using
    allocate_next (returned env left) right false registered (returned_frame env left frame)
      (fun second => NativeM.ok (first, second))

end Returned.Framed
