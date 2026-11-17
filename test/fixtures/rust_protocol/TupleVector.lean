module
public import __PREFIX__.Extraction.Funs
public import __PREFIX__.RustlerBridge
public section
open Aeneas Aeneas.Std
namespace __PREFIX__.Properties

@[expose] def replaceHead (rows : List (I64 × U64)) (value : I64) : List (I64 × U64) :=
  match rows with
  | [] => []
  | first :: tail => (value, first.2) :: tail

@[simp] theorem replaceHead_length (rows : List (I64 × U64)) (value : I64) :
    (replaceHead rows value).length = rows.length := by cases rows <;> rfl

@[expose] def updatedSlice (input : Slice (I64 × U64)) (value : I64) : Slice (I64 × U64) :=
  Slice.from (replaceHead input.val value) (by simp)

@[expose] def updatedVector (input : alloc.vec.Vec (I64 × U64)) (value : I64) :
    alloc.vec.Vec (I64 × U64) :=
  ⟨updatedSlice input.slice value⟩

theorem slice_transition (input : Slice (I64 × U64)) (value : I64) :
    __CORE__.replace_slice_first_pair input value =
      RustM.ok (!input.val.isEmpty, updatedSlice input value) := by
  cases shape : input.val with
  | nil =>
    have unchanged : updatedSlice input value = input := by
      apply Slice.ext
      simp [updatedSlice, replaceHead, shape]
    simp [__CORE__.replace_slice_first_pair, core.slice.Slice.is_empty, shape, unchanged]
  | cons first tail =>
    rcases first with ⟨signed, unsigned⟩
    simp [__CORE__.replace_slice_first_pair, core.slice.Slice.is_empty, shape, replaceHead,
      Slice.index_mut_usize, Slice.index_usize, Slice.set, Slice.setAtNat, updatedSlice]

theorem vector_transition (input : alloc.vec.Vec (I64 × U64)) (value : I64) :
    __CORE__.replace_first_pair input value =
      RustM.ok (!input.val.isEmpty, updatedVector input value) := by
  simp [__CORE__.replace_first_pair, alloc.vec.Vec.deref_mut, lift, slice_transition, alloc.vec.Vec.val, updatedVector]

theorem composition (input : alloc.vec.Vec (I64 × U64)) (value : I64) :
    __ANALYSIS__.replace_first_pair input value =
      RustM.ok (!input.val.isEmpty, updatedVector input value) := vector_transition input value

theorem preserves_fields (input : alloc.vec.Vec (I64 × U64)) (value : I64) :
    ∃ changed updated, __ANALYSIS__.replace_first_pair input value = RustM.ok (changed, updated) ∧
      updated.val = replaceHead input.val value ∧
      updated.val.map Prod.snd = input.val.map Prod.snd ∧
      updated.val.tail = input.val.tail ∧ updated.val.length = input.val.length := by
  rw [composition]
  refine ⟨_, _, rfl, ?_, ?_, ?_, ?_⟩ <;>
    cases shape : input.slice.val <;> simp [updatedVector, updatedSlice, alloc.vec.Vec.val, replaceHead, shape]

theorem facade_spec (input : alloc.vec.Vec (I64 × U64)) (value : I64) :
    __FACADE__ input value = RustM.ok (!input.val.isEmpty, updatedVector input value) := by
  simpa [__FACADE__] using composition input value

-- Matches the generated two-field codec for these decoding proofs.
abbrev decodeRecord (input : Lynx.Term) : Except Lynx.Exception (I64 × U64) := do
  let fields ← Lynx.Rustler.decodeTuple 2 input
  let first ← Lynx.Rustler.tupleField fields 0
  let signed ← Lynx.Rustler.decodeSigned .I64 64 first
  let second ← Lynx.Rustler.tupleField fields 1
  let unsigned ← Lynx.Rustler.decodeUnsigned .U64 64 second
  pure (signed, unsigned)

@[expose] def inputVector : alloc.vec.Vec (I64 × U64) :=
  alloc.vec.Vec.from [((-1)#i64, 18446744073709551615#u64), (42#i64, 9#u64)] (by simp; scalar_tac)

@[expose] def boundaryVector : alloc.vec.Vec (I64 × U64) :=
  alloc.vec.Vec.from [((-9223372036854775808)#i64, 0#u64)] (by simp; scalar_tac)

theorem input_decoded : Lynx.Rustler.decodeScalarVec decodeRecord
    (.cons (.tuple #[.integer (-1), .integer 18446744073709551615])
      (.cons (.tuple #[.integer 42, .integer 9]) .nil)) = .ok inputVector := by
  unfold inputVector
  apply Lynx.Rustler.decodeScalarVec_values _
    (inputs := [.tuple #[.integer (-1), .integer 18446744073709551615], .tuple #[.integer 42, .integer 9]])
    ?_ (by decide) (by simp; scalar_tac)
  exact .cons (by rfl) (.cons (by rfl) .nil)

theorem boundary_decoded : Lynx.Rustler.decodeScalarVec decodeRecord
    (.cons (.tuple #[.integer (-9223372036854775808), .integer 0]) .nil) =
      .ok boundaryVector := by
  unfold boundaryVector
  apply Lynx.Rustler.decodeScalarVec_values _
    (inputs := [.tuple #[.integer (-9223372036854775808), .integer 0]])
    ?_ (by decide) (by simp; scalar_tac)
  exact .cons (by rfl) .nil

theorem wrong_arity (tail : Lynx.Term) :
    Lynx.Rustler.decodeScalarVec decodeRecord (.cons (.tuple #[.integer 1]) tail) =
      .error (.error (.atom "badarg")) :=
  Lynx.Rustler.decodeScalarVec_headError _ _ _ _ rfl

theorem unsigned_range (tail : Lynx.Term) :
    Lynx.Rustler.decodeScalarVec decodeRecord
      (.cons (.tuple #[.integer 0, .integer 18446744073709551616]) tail) =
      .error (.error (.atom "badarg")) :=
  Lynx.Rustler.decodeScalarVec_headError _ _ _ _ rfl

theorem signed_range (tail : Lynx.Term) :
    Lynx.Rustler.decodeScalarVec decodeRecord
      (.cons (.tuple #[.integer 9223372036854775808, .integer 0]) tail) =
      .error (.error (.atom "badarg")) :=
  Lynx.Rustler.decodeScalarVec_headError _ _ _ _ rfl

theorem bad_head (tail : Lynx.Term) :
    Lynx.Rustler.decodeScalarVec decodeRecord
      (.cons (.tuple #[.atom "invalid", .integer 0]) tail) =
      .error (.error (.atom "badarg")) :=
  Lynx.Rustler.decodeScalarVec_headError _ _ _ _ rfl

theorem improper (tail : Int) :
    Lynx.Rustler.decodeScalarVec decodeRecord
      (.cons (.tuple #[.integer 1, .integer 0]) (.integer tail)) =
      .error (.error (.atom "nif_panicked")) :=
  Lynx.Rustler.decodeScalarVec_improper _ _ (1#i64, 0#u64) _ rfl

theorem non_list : Lynx.Rustler.decodeScalarVec decodeRecord (.atom "invalid") =
    .error (.error (.atom "badarg")) :=
  Lynx.Rustler.decodeScalarVec_notList _ _ (by simp) (by simp)

theorem decoding_budget {inputs : List Lynx.Term} {values : List (I64 × U64)}
    (decoded : List.Forall₂ (fun input value => decodeRecord input = .ok value) inputs values)
    (large : Lynx.Rustler.byteVecLimit < values.length) :
    Lynx.Rustler.decodeScalarVec decodeRecord (Lynx.Term.list inputs) = .error .exhausted :=
  Lynx.Rustler.decodeScalarVec_exhausted _ decoded large

end __PREFIX__.Properties
