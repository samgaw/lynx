module
public import OwnedText.Extraction.Funs
public import OwnedText.RustlerBridge
public section
open Aeneas Aeneas.Std experiment_nif
namespace OwnedText.Properties
open OwnedText.Extraction

theorem decode_invalid (input : alloc.vec.Vec U8) (error : core.str.error.Utf8Error)
    (invalid : Bytes.fromUtf8 input.slice = .ok (.Err error)) :
    experiment_core.protocol.decode_owned input = .ok (.Err input) := by
  simp [experiment_core.protocol.decode_owned,OwnedString.fromUtf8,invalid,OwnedString.errorIntoBytes]

theorem composition (input : alloc.vec.Vec U8) :
    experiment_analysis.decode_owned input = experiment_core.protocol.decode_owned input := by
  rfl

@[expose] def broken : alloc.vec.Vec U8 := ⟨Slice.from [195#u8,40#u8] (by scalar_tac)⟩
theorem invalid_bytes : experiment_analysis.decode_owned broken = .ok (.Err broken) := by cbv
theorem non_ascii : experiment_analysis.decode_owned ⟨toStr "héllo"⟩ = .ok (.Ok "héllo") := by cbv

theorem facade_unicode : __FACADE__ ⟨#[104,195,169]⟩ = .ok (.Ok "hé") := by cbv
theorem facade_invalid : __FACADE__ ⟨#[195,40]⟩ = .ok (.Err broken) := by cbv
end OwnedText.Properties
