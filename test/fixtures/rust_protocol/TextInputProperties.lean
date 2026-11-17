module
public import TextInput.Extraction.Funs
public import TextInput.RustlerBridge
public import TextInput.BorrowedProperties
public section
open Aeneas Aeneas.Std experiment_nif
namespace TextInput.Properties

theorem unmarked (text : String) : experiment_analysis.decorate_owned text false = .ok text := by
  rfl

theorem marked (text : String) (bound : (text ++ "!").toByteArray.size ≤ 262144) :
    experiment_analysis.decorate_owned text true = .ok (text ++ "!") := by
  have suffix : String.fromUTF8? ⟨((toStr "!").val.map (fun byte => UInt8.ofNat byte.val)).toArray⟩ = some "!" := by decide +kernel
  simp only [experiment_analysis.decorate_owned,↓reduceIte,experiment_core.protocol.append_owned,
    TextInput.Extraction.OwnedString.pushStr,suffix,bound]

theorem exceeds_spec (text : String) (budget : Usize)
    (bound : (TextInput.Extraction.OwnedString.byteList text).length ≤ Usize.max) :
    experiment_core.protocol.owned_exceeds text budget = .ok (decide (budget.val < (TextInput.Extraction.OwnedString.byteList text).length)) := by
  simp [experiment_core.protocol.owned_exceeds, TextInput.Extraction.OwnedString.intoBytes,
    bound, alloc.vec.Vec.val]

theorem nonempty_spec (text : String)
    (bound : (TextInput.Extraction.OwnedString.byteList text).length ≤ Usize.max) :
    experiment_analysis.owned_nonempty text = .ok (decide (0 < (TextInput.Extraction.OwnedString.byteList text).length)) := by
  simp [experiment_analysis.owned_nonempty,experiment_core.protocol.owned_exceeds,
    TextInput.Extraction.OwnedString.intoBytes,bound,alloc.vec.Vec.val]

theorem nonempty_unicode : experiment_analysis.owned_nonempty "hé" = .ok true := by
  have count : (TextInput.Extraction.OwnedString.byteList "hé").length = 3 := by decide +kernel
  have bound : (TextInput.Extraction.OwnedString.byteList "hé").length ≤ Usize.max := by
    rw [count]
    cases System.Platform.numBits_eq <;> scalar_tac
  have positive : decide (0 < (3 : Nat)) = true := by decide +kernel
  simpa only [count,positive] using nonempty_spec "hé" bound

theorem empty_text : experiment_analysis.owned_nonempty "" = .ok false := by
  have bound : (TextInput.Extraction.OwnedString.byteList "").length ≤ Usize.max := by simp [TextInput.Extraction.OwnedString.byteList]
  simpa [TextInput.Extraction.OwnedString.byteList] using nonempty_spec "" bound

theorem facade_marked : __DECORATE__ "hé" true = .ok "hé!" := by
  simpa [__DECORATE__] using marked "hé" (by decide +kernel)
theorem facade_unmarked (text : String) : __DECORATE__ text false = .ok text := by
  simp [__DECORATE__,unmarked]
theorem facade_nonempty : __NONEMPTY__ "hé" = .ok true := by
  simpa [__NONEMPTY__] using nonempty_unicode
theorem facade_borrowed_echo (text : Str) : __BORROWED_ECHO__ text = .ok text := by
  rfl

theorem facade_borrowed_short (text : Str) (short : text.val.length < 4) :
    __TEXT_HEADER__ text = .ok none := by
  exact TextInput.BorrowedProperties.borrowed_header_short text short

theorem facade_borrowed_word : __TEXT_HEADER__ (toStr "LYNX!") = .ok (some 1280921176#u32) := by
  exact TextInput.BorrowedProperties.borrowed_network_order

theorem facade_borrowed_option (value : Option Str × Bool) :
    __BORROWED_OPTION__ value = .ok value := by
  rfl

end TextInput.Properties
