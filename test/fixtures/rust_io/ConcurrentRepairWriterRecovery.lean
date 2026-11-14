module
public import Record.ConcurrentRepairWriterInvariant
public import Record.EncodedPrefixRecovery
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.ConcurrentRepairWriterRecovery
open NativeFile Record.Properties Record.CrashProperties Record.LogProperties Record.RecoveryProperties
  Record.RepairCrashProperties Record.RepeatedRepairProperties Record.ResizeProperties Record.EncodedPrefixRecovery Record.RepairWriterObserver
  Record.ConcurrentRepairWriterInvariant

private theorem bytes_equal (left right : ByteArray) (equal : (left == right) = true) : left = right := by
  change (left.data == right.data) = true at equal
  exact ByteArray.ext (by simpa only [beq_iff_eq] using equal)

private theorem same_prefix (data : ByteArray) : Prefix data data := ⟨le_rfl, fun _ _ => rfl⟩

private theorem base_image (data : ByteArray) (admitted : admittedBytes data = true) :
    Prefix original data ∧ data.size ≤ limit := by
  simp only [admittedBytes, Bool.or_eq_true] at admitted
  rcases admitted with ((((a | a) | a) | a) | a) | a
  · obtain rfl := bytes_equal _ _ a
    exact ⟨prefix_append _ _, by decide⟩
  · obtain rfl := bytes_equal _ _ a
    exact ⟨same_prefix _, by decide⟩
  · obtain rfl := bytes_equal _ _ a
    exact ⟨by simpa [original, firstOnly, logBytes, List.append_assoc] using prefix_append (logBytes [13#u16]) (logBytes [19#u16]), by decide⟩
  · obtain rfl := bytes_equal _ _ a
    exact ⟨by simpa [original, secondOnly, logBytes, List.append_assoc] using prefix_append (logBytes [13#u16]) (logBytes [23#u16]), by decide⟩
  · obtain rfl := bytes_equal _ _ a
    exact ⟨by simpa [original, ordered, logBytes, List.append_assoc] using prefix_append (logBytes [13#u16]) (logBytes [19#u16, 23#u16]), by decide⟩
  · obtain rfl := bytes_equal _ _ a
    exact ⟨by simpa [original, reversed, logBytes, List.append_assoc] using prefix_append (logBytes [13#u16]) (logBytes [23#u16, 19#u16]), by decide⟩

private theorem first_prefix (data : ByteArray) (admitted : (data == firstOnly || data == ordered) = true) :
    Prefix firstOnly data := by
  simp only [Bool.or_eq_true] at admitted
  rcases admitted with a | a
  · obtain rfl := bytes_equal _ _ a; exact same_prefix _
  · obtain rfl := bytes_equal _ _ a
    simpa [firstOnly, ordered, logBytes, List.append_assoc] using prefix_append (logBytes [13#u16, 19#u16]) (logBytes [23#u16])

private theorem second_prefix (data : ByteArray) (admitted : (data == secondOnly || data == reversed) = true) :
    Prefix secondOnly data := by
  simp only [Bool.or_eq_true] at admitted
  rcases admitted with a | a
  · obtain rfl := bytes_equal _ _ a; exact same_prefix _
  · obtain rfl := bytes_equal _ _ a
    simpa [secondOnly, reversed, logBytes, List.append_assoc] using prefix_append (logBytes [13#u16, 23#u16]) (logBytes [19#u16])

/-- A shared encoded prefix contains every observed acknowledgement. Observation
order is irrelevant, and a prefix may also include an unobserved durable append. -/
private theorem common_records (env : Environment) (file : State)
    (v : admittedBytes file.visible = true) (d : admittedBytes file.durable = true)
    (first : (!acknowledged 19 env || firstProtected file.visible file.durable) = true)
    (second : (!acknowledged 23 env || secondProtected file.visible file.durable) = true)
    (both : (!(acknowledged 19 env && acknowledged 23 env) || bothProtected file.visible file.durable) = true) :
    ∃ values : List U16, values.length ≤ 262144 ∧ 13#u16 ∈ values ∧
      (acknowledged 19 env = true → 19#u16 ∈ values) ∧
      (acknowledged 23 env = true → 23#u16 ∈ values) ∧
      Prefix (disk (logBytes values)) file.visible ∧ Prefix (disk (logBytes values)) file.durable := by
  by_cases a : acknowledged 19 env = true
  · by_cases b : acknowledged 23 env = true
    · have protectedImages : bothProtected file.visible file.durable = true := by simpa [a, b] using both
      simp only [bothProtected, Bool.or_eq_true, Bool.and_eq_true] at protectedImages
      rcases protectedImages with pair | pair
      · obtain ⟨v, d⟩ := pair
        obtain v := bytes_equal _ _ v; obtain d := bytes_equal _ _ d
        refine ⟨[13#u16,19#u16,23#u16], by decide, by simp, by simp, by simp, ?_, ?_⟩
        · rw [v]; exact same_prefix _
        · rw [d]; exact same_prefix _
      · obtain ⟨v, d⟩ := pair
        obtain v := bytes_equal _ _ v; obtain d := bytes_equal _ _ d
        refine ⟨[13#u16,23#u16,19#u16], by decide, by simp, by simp, by simp, ?_, ?_⟩
        · rw [v]; exact same_prefix _
        · rw [d]; exact same_prefix _
    · have protectedImages : firstProtected file.visible file.durable = true := by simpa [a] using first
      simp only [firstProtected, Bool.or_eq_true, Bool.and_eq_true] at protectedImages
      rcases protectedImages with pair | pair
      · refine ⟨[13#u16,19#u16], by decide, by simp, by simp, by simp [b], ?_, ?_⟩
        · exact first_prefix _ (by simpa only [Bool.or_eq_true] using pair.1)
        · exact first_prefix _ (by simpa only [Bool.or_eq_true] using pair.2)
      · have v := bytes_equal _ _ pair.1; have d := bytes_equal _ _ pair.2
        refine ⟨[13#u16,23#u16,19#u16], by decide, by simp, by simp, by simp, ?_, ?_⟩
        · rw [v]; exact same_prefix _
        · rw [d]; exact same_prefix _
  · by_cases b : acknowledged 23 env = true
    · have protectedImages : secondProtected file.visible file.durable = true := by simpa [b] using second
      simp only [secondProtected, Bool.or_eq_true, Bool.and_eq_true] at protectedImages
      rcases protectedImages with pair | pair
      · refine ⟨[13#u16,23#u16], by decide, by simp, by simp [a], by simp, ?_, ?_⟩
        · exact second_prefix _ (by simpa only [Bool.or_eq_true] using pair.1)
        · exact second_prefix _ (by simpa only [Bool.or_eq_true] using pair.2)
      · have v := bytes_equal _ _ pair.1; have d := bytes_equal _ _ pair.2
        refine ⟨[13#u16,19#u16,23#u16], by decide, by simp, by simp, by simp, ?_, ?_⟩
        · rw [v]; exact same_prefix _
        · rw [d]; exact same_prefix _
    · exact ⟨[13#u16], by decide, by simp, by simp [a], by simp [b], (base_image _ v).1, (base_image _ d).1⟩

/-- Every admitted crash at every raw prefix permits actual Rust recovery of a
complete prefix containing all observed acknowledgements. Unacknowledged suffix
bytes may remain; this bounded read neither assumes nor promises their repair. -/
theorem recover_acknowledgements (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config Term)
    (run : Concurrent.Run (.start initial
      (callers (locked_repair_and_append ⟨1⟩ 4#usize 19#u16)
        (locked_repair_and_append ⟨1⟩ 4#usize 23#u16)) elapsed) events last)
    (mask : ByteArray) (image : Image) (rest : Term)
    (captured : crashImage ⟨2⟩ mask (snapshot last) = some image) :
    ∃ (values : List U16) (capacity : values.length ≤ 262144), 13#u16 ∈ values ∧
      (acknowledged 19 (snapshot last) = true → 19#u16 ∈ values) ∧
      (acknowledged 23 (snapshot last) = true → 23#u16 ∈ values) ∧
      recover_log ⟨image.highWater + 1⟩ (Usize.ofNatCore values.length (by scalar_tac))
        (restarted image (recoveryScript image.bytes rest)) =
        (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)), ⟨image.highWater + 1⟩),
          fileEnv ({} : Environment) ⟨image.highWater + 1⟩
            (scanning image.bytes rest (4 * values.length)) []) := by
  have checked := Concurrent.checkInvariant_sound (prefixes_checked elapsed) run
  simp only [safe, Bool.and_eq_true] at checked
  have retained := checked.1
  unfold Record.ConcurrentRepairWriterInvariant.retained at retained
  dsimp only at retained
  split at retained
  · rename_i file found
    simp only [Bool.and_eq_true] at retained
    obtain ⟨values, capacity, original, first, second, v, d⟩ := common_records (snapshot last) file
      retained.1.1.1.1 retained.1.1.1.2 retained.1.1.2 retained.1.2 retained.2
    unfold crashImage at captured
    rw [found] at captured
    change (persist file.durable file.visible mask).bind
      (fun bytes => some (⟨bytes, (snapshot last).nativeRefCounter⟩ : Image)) = some image at captured
    obtain ⟨bytes, persisted, equal⟩ := Option.bind_eq_some_iff.mp captured
    cases Option.some.inj equal
    have kept := persist_prefix _ _ _ _ _ d v persisted
    have sizes := persist_lengths _ _ _ _ persisted
    have vb := (base_image _ retained.1.1.1.1).2
    have db := (base_image _ retained.1.1.1.2).2
    exact ⟨values, capacity, original, first, second,
      restart_prefix values _ rest kept (by dsimp; omega) capacity⟩
  · contradiction

/-- Completion requires both observed successes, a released mutex and a fully
synchronized serial log. It is derived from the same all-prefix certificate. -/
theorem terminal_accepted (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config Term) (outcome : Outcome Term)
    (run : Concurrent.Run (.start initial
      (callers (locked_repair_and_append ⟨1⟩ 4#usize 19#u16)
        (locked_repair_and_append ⟨1⟩ 4#usize 23#u16)) elapsed) events last)
    (terminal : Concurrent.Terminal last outcome) : accepted last = true := by
  have kept := Concurrent.checkInvariant_sound (prefixes_checked elapsed) run
  simp only [safe, Bool.and_eq_true] at kept
  simpa only [terminal.successors_eq_nil, List.isEmpty_nil, Bool.not_true,
    Bool.false_or] using kept.2

/-- Once both writers finish, every admitted crash leaves precisely one of the
two serial logs. A fresh actual Rust repair returns and synchronizes that log. -/
theorem terminal_recovery (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config Term) (outcome : Outcome Term)
    (run : Concurrent.Run (.start initial
      (callers (locked_repair_and_append ⟨1⟩ 4#usize 19#u16)
        (locked_repair_and_append ⟨1⟩ 4#usize 23#u16)) elapsed) events last)
    (terminal : Concurrent.Terminal last outcome)
    (mask : ByteArray) (image : Image) (rest : Term)
    (captured : crashImage ⟨2⟩ mask (snapshot last) = some image) :
    ∃ (values : List U16) (capacity : values.length ≤ 262144),
      (values = [13#u16, 19#u16, 23#u16] ∨ values = [13#u16, 23#u16, 19#u16]) ∧
      image.bytes = disk (logBytes values) ∧
      repair_log ⟨image.highWater + 1⟩ 4#usize (restarted image (repairScript image.bytes rest)) =
        (.ok (.Ok (some (alloc.vec.Vec.from values (by scalar_tac))), ⟨image.highWater + 1⟩),
          fileEnv ({} : Environment) ⟨image.highWater + 1⟩
            ⟨disk (logBytes values), disk (logBytes values), image.bytes.size, rest⟩ []) := by
  have accepted := terminal_accepted elapsed events last outcome run terminal
  unfold Record.ConcurrentRepairWriterInvariant.accepted at accepted
  dsimp only at accepted
  generalize output : last.outcome = reply at accepted
  split at accepted
  · rename_i file found
    simp only [Bool.and_eq_true] at accepted
    unfold crashImage at captured
    rw [found] at captured
    change (persist file.durable file.visible mask).bind
      (fun bytes => some (⟨bytes, (snapshot last).nativeRefCounter⟩ : Image)) = some image at captured
    obtain ⟨bytes, persisted, equal⟩ := Option.bind_eq_some_iff.mp captured
    cases Option.some.inj equal
    have images := accepted.1.1.1
    simp only [Bool.or_eq_true, Bool.and_eq_true] at images
    rcases images with pair | pair
    · rw [bytes_equal _ _ pair.1, bytes_equal _ _ pair.2] at persisted
      have same := persist_same ordered mask bytes persisted
      refine ⟨[13#u16,19#u16,23#u16], by decide, Or.inl rfl, same, ?_⟩
      apply restart_repair _ _ rest 4#usize
      · rw [same]
        simpa only [ordered, List.append_nil] using log_image [13#u16,19#u16,23#u16] [] (by decide)
      · rw [same]; dsimp only; decide
      · decide
    · rw [bytes_equal _ _ pair.1, bytes_equal _ _ pair.2] at persisted
      have same := persist_same reversed mask bytes persisted
      refine ⟨[13#u16,23#u16,19#u16], by decide, Or.inr rfl, same, ?_⟩
      apply restart_repair _ _ rest 4#usize
      · rw [same]
        simpa only [reversed, List.append_nil] using log_image [13#u16,23#u16,19#u16] [] (by decide)
      · rw [same]; dsimp only; decide
      · decide
  · contradiction

end Record.ConcurrentRepairWriterRecovery
