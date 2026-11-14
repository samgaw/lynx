module
public import Record.RepeatedRepairProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.RepairInvariantProperties
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.AppendProperties
  Record.LogProperties Record.TailProperties Record.ResizeProperties
  Record.RepairCrashProperties Record.RepeatedRepairProperties

abbrev Reply := core.result.Result (Option (alloc.vec.Vec U16)) NativeIoError × NativeFile

@[expose] def complete : ByteArray := disk (logBytes [13#u16])
@[expose] def original : ByteArray := disk (logBytes [13#u16] ++ [7#u8])
@[expose] def padded : ByteArray := disk (logBytes [13#u16] ++ [0#u8])

@[expose] def retained (data : ByteArray) : Bool :=
  data.data == complete.data || data.data == original.data || data.data == padded.data

@[expose] def world : Concurrent.Config Reply → Environment
  | .start env .. => env
  | .running state .. => state.nativeView []

@[expose] def safe (config : Concurrent.Config Reply) : Bool :=
  match lookup ⟨1⟩ (world config) with
  | some state => retained state.visible && retained state.durable && decide (state.position ≤ limit)
  | none => false

@[expose] def initial (mask : ByteArray) : Environment :=
  fileEnv {} ⟨1⟩ ⟨original, original, 0, interruptionScript original mask .nil⟩ []

private theorem bytes_eq {left right : ByteArray} (size : left.size = right.size)
    (bytes : ∀ i, i < left.size → left[i]! = right[i]!) : left = right := by
  apply ByteArray.ext
  apply _root_.Array.ext
  · exact size
  · intro i hi hj
    have il : i < left.size := hi
    have ir : i < right.size := hj
    simpa only [getElem!_pos left i il, getElem!_pos right i ir,
      ByteArray.getElem_eq_getElem_data] using bytes i il

private theorem resize_images (mask result : ByteArray)
    (accepted : persist original complete mask = some result) :
    result = complete ∨ result = original ∨ result = padded := by
  have sizes := Record.RepairCrashProperties.persist_lengths _ _ _ _ accepted
  change 4 ≤ result.size ∧ result.size ≤ 5 at sizes
  have lower := sizes.1
  have upper := sizes.2
  have head (i : Nat) (inside : i < 4) : result[i]! = complete[i]! := by
    have entry := Record.CrashProperties.persist_at original complete mask result accepted i (by omega)
    have indices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases indices with rfl | rfl | rfl | rfl
    all_goals split at entry <;> exact entry
  by_cases four : result.size = 4
  · exact .inl (bytes_eq (by exact four) (by
      intro i inside
      exact head i (by omega)))
  · have five : result.size = 5 := by omega
    have entry := Record.CrashProperties.persist_at original complete mask result accepted 4 (by omega)
    by_cases choice : mask[4]! == 1
    · right; right
      apply bytes_eq (by exact five)
      intro i inside
      by_cases last : i = 4
      · subst i
        rw [ite_eq_left choice] at entry
        exact entry
      · have before : i < 4 := by omega
        have same : complete[i]! = padded[i]! := by
          have indices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
          rcases indices with rfl | rfl | rfl | rfl <;> rfl
        exact (head i before).trans same
    · right; left
      apply bytes_eq (by exact five)
      intro i inside
      by_cases last : i = 4
      · subst i
        rw [ite_eq_right choice] at entry
        exact entry
      · have before : i < 4 := by omega
        have same : complete[i]! = original[i]! := by
          have indices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
          rcases indices with rfl | rfl | rfl | rfl <;> rfl
        exact (head i before).trans same

private def beforeResize (mask : ByteArray) : NativeFile.State :=
  ⟨original, original, 5, outcome "set_len" true 0 mask (.cons (.atom "blocked") .nil)⟩

private theorem resize_step (mask : ByteArray) :
    setLenStep (beforeResize mask) 4#u64 =
      (persist original complete mask).map fun durable =>
        (.Ok (), ⟨complete, durable, 5, .cons (.atom "blocked") .nil⟩) := by
  have shrunk : resize original 4 = complete := by decide
  simp [beforeResize, setLenStep, action, outcome, limit, shrunk, Option.map_eq_bind]

section
attribute [local cbv_opaque] Lynx.NativeFile.setLenStep
set_option maxRecDepth 8192 in
set_option maxHeartbeats 64000000 in
set_option cbv.maxSteps 100000 in
/-- Every resize mask preserves the record throughout the actual Rust call.
Malformed choices may exhaust verification; this proves safety, not completion. -/
theorem mask_checked (mask : ByteArray) (elapsed : PID → Nat → Nat) :
    Concurrent.checkInvariant safe 96
      (.start (initial mask) (repair_log ⟨1⟩ 3#usize) elapsed) = true := by
  have transition := resize_step mask
  conv at transition => lhs; cbv
  cbv
  simp only [transition]
  by_cases absent : persist original complete mask = none
  · simp only [absent]
    cbv
  · have available := Option.ne_none_iff_exists.mp absent
    rcases available with ⟨image, accepted⟩
    simp only [← accepted]
    have images := resize_images mask image accepted.symm
    rcases images with rfl | rfl | rfl
    all_goals cbv
end

theorem retained_shape (data : ByteArray) (kept : retained data = true) :
    LogImage [13#u16] data ∧ data.size ≤ limit := by
  simp only [retained, Bool.or_eq_true, beq_iff_eq] at kept
  rcases kept with (kept | kept) | kept
  all_goals have equal := ByteArray.ext kept; subst data
  · exact ⟨by simpa only [complete, List.append_nil] using log_image [13#u16] [] (by decide), by decide⟩
  · exact ⟨log_image _ _ (by decide), by decide⟩
  · exact ⟨log_image _ _ (by decide), by decide⟩

/-- Any allowed power loss at a checked prefix retains the complete record.
The crash mask is arbitrary; no successful Rust return is needed. -/
theorem prefix_image (config : Concurrent.Config Reply) (mask : ByteArray) (image : Image)
    (checked : safe config = true)
    (captured : crashImage ⟨1⟩ mask (world config) = some image) :
    LogImage [13#u16] image.bytes ∧ image.bytes.size ≤ limit := by
  unfold safe at checked
  split at checked
  · rename_i state found
    simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
    have visible := retained_shape state.visible checked.1.1
    have durable := retained_shape state.durable checked.1.2
    unfold crashImage at captured
    rw [found] at captured
    change (persist state.durable state.visible mask).bind
      (fun bytes => some (⟨bytes, (world config).nativeRefCounter⟩ : Image)) = some image at captured
    obtain ⟨bytes, persisted, equal⟩ := Option.bind_eq_some_iff.mp captured
    cases Option.some.inj equal
    have sizes := persist_lengths _ _ _ _ persisted
    exact ⟨persist_log_image _ _ _ _ _ durable.1 visible.1 persisted,
      by have := visible.2; have := durable.2; dsimp; omega⟩
  · contradiction

end Record.RepairInvariantProperties
