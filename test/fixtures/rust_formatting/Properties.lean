module
public import RustWorkspace.NativeFormatting
public import Aeneas.Std.Scalar.Notations
public section
open Aeneas Aeneas.Std
namespace RustWorkspace.Formatting

/-- The writer keeps its existing initial and the actual display value. -/
theorem scalar_renderer (value : U64) (initial : String) :
    (do
      let argument ← Lynx.RustFormatting.core.fmt.rt.Argument.new_display
        { fmt := Lynx.RustFormatting.core.fmt.num.imp.DisplayU64.fmt } value
      argument initial) = Lynx.RustFormatting.Formatting.append initial (toString value.val) := by
  simp [Lynx.RustFormatting.core.fmt.rt.Argument.new_display, Lynx.RustFormatting.core.fmt.num.imp.DisplayU64.fmt, bind_tc_ok]

/-- A terminator does not execute unused arguments. -/
theorem unused_argument : Lynx.RustFormatting.Formatting.run 1 [0] [fun _ => .fail .panic] 0 "initial" =
    RustM.ok (.Ok (), "initial") := by simp [Lynx.RustFormatting.Formatting.run]

/-- UTF-8 lengths count bytes, and a zero inside a literal is not a terminator. -/
theorem utf8_and_nul : Lynx.RustFormatting.Formatting.run 6 [3, 195, 169, 0, 0] [] 0 "" =
    RustM.ok (.Ok (), "é\x00") := by
  have size : "é\x00".utf8ByteSize = 3 := by decide +kernel
  have decoded : String.fromUTF8? ⟨#[195, 169, 0]⟩ = some "é\x00" := by decide +kernel
  simp [Lynx.RustFormatting.Formatting.run, Lynx.RustFormatting.Formatting.writeBytes, Lynx.RustFormatting.Formatting.append, decoded, size]

/-- Both documented literal-length forms have the same output. -/
theorem long_literal : Lynx.RustFormatting.Formatting.run 7 [128, 2, 0, 97, 98, 0] [] 0 "" =
    RustM.ok (.Ok (), "ab") := by
  have size : "ab".utf8ByteSize = 2 := by decide +kernel
  have decoded : String.fromUTF8? ⟨#[97, 98]⟩ = some "ab" := by decide +kernel
  simp [Lynx.RustFormatting.Formatting.run, Lynx.RustFormatting.Formatting.writeBytes, Lynx.RustFormatting.Formatting.append, decoded, size]

/-- The next placeholder receives the next supplied argument. -/
theorem distinct_arguments :
    Lynx.RustFormatting.Formatting.run 6 [192, 1, 58, 192, 0]
      [fun initial => Lynx.RustFormatting.Formatting.append initial "a", fun initial => Lynx.RustFormatting.Formatting.append initial "b"] 0 "" =
      RustM.ok (.Ok (), "a:b") := by
  have a : "a".utf8ByteSize = 1 := by decide +kernel
  have b : "b".utf8ByteSize = 1 := by decide +kernel
  have colon : ":".utf8ByteSize = 1 := by decide +kernel
  have joined : "a:".utf8ByteSize = 2 := by decide +kernel
  have decoded : String.fromUTF8? ⟨#[58]⟩ = some ":" := by decide +kernel
  simp [Lynx.RustFormatting.Formatting.run, Lynx.RustFormatting.Formatting.writeBytes, Lynx.RustFormatting.Formatting.append, decoded, a, b, colon, joined]

/-- A renderer error stops evaluation before a later panicking argument. -/
theorem error_stops : Lynx.RustFormatting.Formatting.run 3 [192, 192, 0]
    [fun initial => .ok (.Err (), initial), fun _ => .fail .panic] 0 "before" =
    RustM.ok (.Err (), "before") := by simp [Lynx.RustFormatting.Formatting.run]

theorem panic_propagates : Lynx.RustFormatting.Formatting.run 2 [192, 0] [fun _ => .fail .panic] 0 "" =
    RustM.fail .panic := by simp [Lynx.RustFormatting.Formatting.run]

/-- Width and other options remain unsupported rather than being ignored. -/
theorem options_cutoff : Lynx.RustFormatting.Formatting.run 4 [194, 5, 0, 0] [] 0 "" =
    RustM.fail .undef := by simp [Lynx.RustFormatting.Formatting.run]

theorem missing_argument_cutoff : Lynx.RustFormatting.Formatting.run 2 [192, 0] [] 0 "" =
    RustM.fail .undef := by simp [Lynx.RustFormatting.Formatting.run]

theorem malformed_length_cutoff : Lynx.RustFormatting.Formatting.run 3 [5, 97, 0] [] 0 "" =
    RustM.fail .undef := by simp [Lynx.RustFormatting.Formatting.run]

theorem invalid_utf8_cutoff : Lynx.RustFormatting.Formatting.run 3 [1, 255, 0] [] 0 "" =
    RustM.fail .undef := by
  have invalid : String.fromUTF8? ⟨#[255]⟩ = none := by decide +kernel
  simp [Lynx.RustFormatting.Formatting.run, Lynx.RustFormatting.Formatting.writeBytes, invalid, bind_tc_fail]

/-- Rust's blanket ToString panics on an erroneous Display implementation. -/
theorem to_string_error :
    Lynx.RustFormatting.alloc.string.ToString.to_string (T := Unit)
      { fmt := fun _ initial => .ok (.Err (), initial) } () = RustM.fail .panic := by
  simp [Lynx.RustFormatting.alloc.string.ToString.to_string, bind_tc_ok]

/-- The public Arguments constructor retains the renderers supplied by extraction. -/
theorem array_arguments :
    (do
      let arguments ← Lynx.RustFormatting.core.fmt.Arguments.new
        (Array.make (Usize.ofNat 2) [192#u8, 0#u8])
        (Array.make (Usize.ofNat 1) [fun state => Lynx.RustFormatting.Formatting.append state "actual"])
      Lynx.RustFormatting.core.fmt.Formatter.write_fmt "" arguments) = RustM.ok (.Ok (), "actual") := by
  have size : "actual".utf8ByteSize = 6 := by decide +kernel
  have program : (⟨#[192, 0]⟩ : ByteArray).toList = [192, 0] := by decide +kernel
  simp [Lynx.RustFormatting.core.fmt.Arguments.new, Lynx.RustFormatting.core.fmt.Formatter.write_fmt, Lynx.RustFormatting.Formatting.bytes,
    Lynx.RustFormatting.Formatting.run, Lynx.RustFormatting.Formatting.validTemplate, Lynx.RustFormatting.Formatting.append, Array.make, size, program]

/-- ToString returns the actual writer output rather than an erased placeholder. -/
theorem to_string_output :
    Lynx.RustFormatting.alloc.string.ToString.to_string { fmt := Lynx.RustFormatting.alloc.string.DisplayString.fmt } "actual" =
      RustM.ok "actual" := by
  have size : "actual".utf8ByteSize = 6 := by decide +kernel
  simp [Lynx.RustFormatting.alloc.string.ToString.to_string, Lynx.RustFormatting.alloc.string.DisplayString.fmt, Lynx.RustFormatting.Formatting.append, size]

theorem to_string_panic :
    Lynx.RustFormatting.alloc.string.ToString.to_string (T := Unit)
      { fmt := fun _ _ => .fail .panic } () = RustM.fail .panic := by
  simp [Lynx.RustFormatting.alloc.string.ToString.to_string]

/-- The size boundary is a cutoff for arbitrary strings; no huge allocation is needed to test it. -/
theorem output_bound (initial text : String)
    (large : 4294967295 < (initial ++ text).toUTF8.size) :
    Lynx.RustFormatting.Formatting.append initial text = RustM.fail .undef := by
  simp only [Lynx.RustFormatting.Formatting.append, ite_eq_right (Nat.not_le_of_lt large)]


/-- Unsafe construction cannot succeed with a missing argument, even if never rendered. -/
theorem constructor_missing_argument : Lynx.RustFormatting.core.fmt.Arguments.new
    (Array.make (Usize.ofNat 2) [192#u8, 0#u8])
    (Array.make (Usize.ofNat 0) []) = RustM.fail .undef := by
  have bytes : (Lynx.RustFormatting.Formatting.bytes [192#u8, 0#u8]).toList = [192, 0] := by decide +kernel
  simp [Lynx.RustFormatting.core.fmt.Arguments.new, Array.make, bytes, Lynx.RustFormatting.Formatting.validTemplate]

theorem valid_utf8_template : Lynx.RustFormatting.Formatting.validTemplate 5 [2, 195, 169, 0] 0 0 = true := by
  decide +kernel

theorem invalid_utf8_template : Lynx.RustFormatting.Formatting.validTemplate 4 [1, 255, 0] 0 0 = false := by
  decide +kernel

theorem missing_terminator : Lynx.RustFormatting.Formatting.validTemplate 3 [1, 97] 0 0 = false := by
  decide +kernel

theorem trailing_bytes : Lynx.RustFormatting.Formatting.validTemplate 3 [0, 0] 0 0 = false := by
  decide +kernel

theorem unsupported_template_options : Lynx.RustFormatting.Formatting.validTemplate 5 [194, 5, 0, 0] 0 0 = false := by
  decide +kernel

end RustWorkspace.Formatting
