module
public import FileResource.Publish
public section
open Lynx
namespace FileResource.Persistence
open NativeFile

/-- An admitted image has a length between the original and visible lengths,
with each byte selected from the corresponding original or visible byte. -/
@[expose] def Compatible (original visible data : ByteArray) : Prop :=
  min original.size visible.size ≤ data.size ∧ data.size ≤ max original.size visible.size ∧
    ∀ index, index < data.size → data[index]! = original[index]! ∨ data[index]! = visible[index]!

theorem original_image (original visible : ByteArray) : Compatible original visible original := by
  refine ⟨min_le_left _ _,le_max_left _ _,?_⟩
  intro index inside
  exact Or.inl rfl

/-- Further permitted persistence preserves the original/visible image relation,
even when an earlier operation already persisted some bytes and then failed. -/
theorem preserve (original visible old mask data : ByteArray) (valid : Compatible original visible old)
    (accepted : persist old visible mask = some data) : Compatible original visible data := by
  unfold persist at accepted
  split at accepted
  · rename_i conditions
    cases accepted
    have size : (⟨mask.data.mapIdx fun index choice =>
        if choice == 1 then visible[index]! else old[index]!⟩ : ByteArray).size = mask.size := by
      simp [← ByteArray.size_data]
    refine ⟨?_,?_,?_⟩
    · rw [size]
      have lower := valid.1
      have upper := valid.2.1
      omega
    · rw [size]
      have lower := valid.1
      have upper := valid.2.1
      omega
    · intro index inside
      rw [getElem!_pos (⟨mask.data.mapIdx fun index choice =>
        if choice == 1 then visible[index]! else old[index]!⟩ : ByteArray) index inside]
      simp only [ByteArray.getElem_eq_getElem_data,_root_.Array.getElem_mapIdx]
      split
      · exact Or.inr rfl
      · by_cases previous : index < old.size
        · exact valid.2.2 index previous
        · by_cases originalInside : index < original.size
          · have outside : ¬ index < visible.size := by have lower := valid.1; omega
            right
            rw [getElem!_neg old index previous,getElem!_neg visible index outside]
          · left
            rw [getElem!_neg old index previous,getElem!_neg original index originalInside]
  · contradiction

/-- Reconstruct a concrete old/new mask from an admitted image. -/
@[expose] def choices (visible data : ByteArray) : ByteArray :=
  ⟨data.data.mapIdx fun index byte => if byte == visible[index]! then 1 else 0⟩

theorem realize (original visible data : ByteArray) (valid : Compatible original visible data) :
    persist original visible (choices visible data) = some data := by
  have size : (choices visible data).size = data.size := by simp [choices,← ByteArray.size_data]
  have bits : ((choices visible data).data.toList.all (fun byte => byte == 0 || byte == 1)) = true := by
    apply List.all_eq_true.mpr
    intro byte member
    have mapped : byte ∈ data.data.mapIdx (fun index byte => if byte == visible[index]! then (1 : UInt8) else 0) := by
      simpa [choices] using member
    obtain ⟨index,inside,rfl⟩ := _root_.Array.mem_mapIdx.mp mapped
    split <;> decide +kernel
  have conditions : min original.size visible.size ≤ (choices visible data).size ∧
      (choices visible data).size ≤ max original.size visible.size ∧
      (((choices visible data).data.toList.all (fun byte => byte == 0 || byte == 1)) = true) := by
    exact ⟨by rw [size]; exact valid.1,by rw [size]; exact valid.2.1,bits⟩
  unfold persist
  rw [ite_eq_left conditions]
  congr 1
  apply ByteArray.ext
  apply _root_.Array.ext
  · simp [choices]
  · intro index leftBound rightBound
    have inside : index < data.size := by simpa [← ByteArray.size_data] using rightBound
    have current : data.data[index] = data[index]! := by rw [getElem!_pos data index inside]; rfl
    simp only [choices,_root_.Array.getElem_mapIdx]
    rw [current]
    by_cases same : data[index]! = visible[index]!
    · simp [same]
    · have previous := (valid.2.2 index inside).resolve_right same
      simpa [same] using previous.symm

theorem of_persist (original visible mask data : ByteArray)
    (accepted : persist original visible mask = some data) : Compatible original visible data :=
  preserve original visible original mask data (original_image original visible) accepted

/-- Two permitted steps are equivalent to some original/visible image. This
includes failed fsync followed by additional background persistence at crash. -/
theorem compose (original visible first saved second data : ByteArray)
    (initial : persist original visible first = some saved)
    (later : persist saved visible second = some data) :
    ∃ combined, persist original visible combined = some data := by
  exact ⟨choices visible data,realize original visible data (preserve original visible saved second data
    (of_persist original visible first saved initial) later)⟩

theorem visible_image (original visible : ByteArray) :
    persist original visible (choices visible visible) = some visible := by
  apply realize
  refine ⟨min_le_right _ _,le_max_right _ _,?_⟩
  intro index inside
  exact Or.inr rfl

/-- Apply a finite sequence of actual persistence transitions while the visible
image remains fixed. Changes to the visible image require separate reasoning. -/
@[expose] def advance (visible data : ByteArray) : List ByteArray → Option ByteArray
  | [] => some data
  | mask :: rest => do
    let saved ← persist data visible mask
    advance visible saved rest

theorem finite_preserve (original visible data : ByteArray) (masks : List ByteArray)
    (valid : Compatible original visible data) (result : ByteArray)
    (accepted : advance visible data masks = some result) : Compatible original visible result := by
  induction masks generalizing data with
  | nil => cases accepted; exact valid
  | cons mask rest ih =>
    simp only [advance,Bind.bind,Option.bind_eq_some_iff] at accepted
    obtain ⟨saved,step,following⟩ := accepted
    exact ih saved (preserve original visible data mask saved valid step) following

/-- Every finite persistence history has a concrete equivalent original/visible
mask; no intermediate failed-operation image is silently replaced by rollback. -/
theorem finite_compose (original visible : ByteArray) (masks : List ByteArray) (result : ByteArray)
    (accepted : advance visible original masks = some result) :
    ∃ combined, persist original visible combined = some result := by
  exact ⟨choices visible result,realize original visible result
    (finite_preserve original visible original masks (original_image original visible) result accepted)⟩

end FileResource.Persistence
