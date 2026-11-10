module
public import Arguments.Extraction.Funs
public section
open Aeneas Aeneas.Std
namespace Arguments

theorem renderer_spec (value : U64) (initial : String)
    (first_bound : (initial.utf8ByteSize + "n=".utf8ByteSize) ≤ 4294967295)
    (final_bound : (initial.utf8ByteSize + "n=".utf8ByteSize + (toString value.val).utf8ByteSize) ≤ 4294967295) :
    argument_analysis.argument_base.Count.Insts.CoreFmtDisplay.fmt value initial =
      .ok (.Ok (), initial ++ "n=" ++ toString value.val) := by
  change initial.utf8ByteSize + "n=".utf8ByteSize + value.val.repr.utf8ByteSize ≤ 4294967295 at final_bound
  have program : (Lynx.RustFormatting.Formatting.bytes [2#u8, 110#u8, 61#u8, 192#u8, 0#u8]).toList =
      [2, 110, 61, 192, 0] := by decide +kernel
  have decoded : String.fromUTF8? ⟨#[110, 61]⟩ = some "n=" := by decide +kernel
  simp [argument_analysis.argument_base.Count.Insts.CoreFmtDisplay.fmt,
    Lynx.RustFormatting.core.fmt.rt.Argument.new_display, Lynx.RustFormatting.core.fmt.Arguments.new,
    Lynx.RustFormatting.core.fmt.Formatter.write_fmt, Lynx.RustFormatting.core.fmt.DisplayShared.fmt,
    argument_analysis.U64.Insts.CoreFmtDisplay,
    Lynx.RustFormatting.core.fmt.num.imp.DisplayU64.fmt, Array.make, program, Lynx.RustFormatting.Formatting.validTemplate,
    Lynx.RustFormatting.Formatting.run, Lynx.RustFormatting.Formatting.writeBytes, decoded, Lynx.RustFormatting.Formatting.append, first_bound, final_bound]

theorem describe_spec (value : U64)
    (first_bound : ("".utf8ByteSize + "n=".utf8ByteSize) ≤ 4294967295)
    (final_bound : ("".utf8ByteSize + "n=".utf8ByteSize + (toString value.val).utf8ByteSize) ≤ 4294967295) :
    argument_analysis.describe value = .ok ("n=" ++ toString value.val) := by
  simp [argument_analysis.describe, Lynx.RustFormatting.alloc.string.ToString.to_string,
    renderer_spec value "" first_bound final_bound]
theorem formatted_spec (value : U64)
    (first_bound : ("".utf8ByteSize + "n=".utf8ByteSize) ≤ 4294967295)
    (final_bound : ("".utf8ByteSize + "n=".utf8ByteSize + (toString value.val).utf8ByteSize) ≤ 4294967295)
    (native_bound : ("n=" ++ toString value.val).utf8ByteSize ≤ Isize.max.toNat) :
    argument_analysis.formatted value = .ok ("n=" ++ toString value.val) := by
  have program : (Lynx.RustFormatting.Formatting.bytes [192#u8, 0#u8]).toList = [192, 0] := by decide +kernel
  simp [argument_analysis.formatted, argument_analysis.core.hint.must_use, Array.make, Lynx.RustFormatting.alloc.fmt.format,
    Lynx.RustFormatting.core.fmt.rt.Argument.new_display, Lynx.RustFormatting.core.fmt.Arguments.new,
    program, Lynx.RustFormatting.Formatting.validTemplate, Lynx.RustFormatting.Formatting.run,
    renderer_spec value "" first_bound final_bound] <;> simp_all [String.utf8ByteSize_append]

theorem rejected_spec (value : U64) : argument_analysis.rejected value = RustM.fail .panic := by
  have program : (Lynx.RustFormatting.Formatting.bytes [192#u8, 0#u8]).toList = [192, 0] := by decide +kernel
  simp [argument_analysis.rejected, argument_analysis.core.hint.must_use, Array.make, Lynx.RustFormatting.alloc.fmt.format,
    Lynx.RustFormatting.core.fmt.rt.Argument.new_display, Lynx.RustFormatting.core.fmt.Arguments.new,
    program, Lynx.RustFormatting.Formatting.validTemplate, Lynx.RustFormatting.Formatting.run,
    argument_analysis.argument_base.Rejected.Insts.CoreFmtDisplay.fmt]

theorem zero_spec : argument_analysis.describe 0#u64 = .ok "n=0" := by
  have zero : toString (0#u64).val = "0" := by
    change Nat.repr 0 = "0"
    rw [Nat.repr_of_lt (by decide), ← String.toList_inj, String.toList_singleton, (Nat.digitChar_eq_zero.mpr rfl : Nat.digitChar 0 = '0')]
    decide +kernel
  have first_bound : "".utf8ByteSize + "n=".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have final_bound : "".utf8ByteSize + "n=".utf8ByteSize + (toString (0#u64).val).utf8ByteSize ≤
      4294967295 := by rw [zero]; decide +kernel
  have joined : "n=" ++ "0" = "n=0" := by decide +kernel
  simpa only [zero, joined] using describe_spec 0#u64 first_bound final_bound
end Arguments
