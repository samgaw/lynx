module
public import ProducerNative.Properties
public import ProducerNative.RustlerBridge
public section
open Aeneas Aeneas.Std
namespace ProducerNative.NativeProperties

theorem roundtrip (input : ByteArray) (bound : input.size ≤ 65535) :
    __FACADE__ input = RustM.ok (some true) := by
  obtain ⟨bytes, decoded, length⟩ := Lynx.Rustler.binaryAsSlice_spec input
    (by scalar_tac) (by scalar_tac)
  have bounded : bytes.val.length ≤ 65535 := by omega
  simp [__FACADE__, decoded, ProducerNative.Properties.binary_roundtrip bytes bounded]

theorem oversize (input : ByteArray) (lower : 65535 < input.size) (upper : input.size ≤ 65538) :
    __FACADE__ input = RustM.ok none := by
  obtain ⟨bytes, decoded, length⟩ := Lynx.Rustler.binaryAsSlice_spec input
    (by scalar_tac) (by scalar_tac)
  have outside : 65535 < bytes.val.length := by omega
  simp [__FACADE__, decoded, ProducerNative.Properties.roundtrip_oversize bytes outside]

end ProducerNative.NativeProperties
