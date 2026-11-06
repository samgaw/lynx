module
public import Endian.Extraction.Funs
public section
open Aeneas Aeneas.Std experiment_analysis
namespace Endian.Properties

theorem little_roundtrip (value : U32) :
    experiment_core.protocol.little_endian_roundtrip value = RustM.ok value := by
  simp only [experiment_core.protocol.little_endian_roundtrip, lift, bind_ok]
  apply congrArg RustM.ok
  apply UScalar.eq_of_val_eq
  change (BitVec.fromLEBytes ((core.num.U32.to_le_bytes value).val.map U8.bv)).toNat = _
  rw [core.num.U32.to_le_bytes, Array.from_val, List.map_map]
  change (BitVec.fromLEBytes (List.map id value.bv.toLEBytes)).toNat = _
  rw [List.map_id, BitVec.fromLEBytes_toLEBytes (by decide : 32 % 8 = 0)]
  rfl

theorem big_roundtrip (value : U32) :
    experiment_core.protocol.big_endian_roundtrip value = RustM.ok value := by
  simp only [experiment_core.protocol.big_endian_roundtrip, lift, bind_ok]
  apply congrArg RustM.ok
  apply UScalar.eq_of_val_eq
  change (BitVec.fromBEBytes ((core.num.U32.to_be_bytes value).val.map U8.bv)).toNat = _
  rw [core.num.U32.to_be_bytes, Array.from_val]
  simp only [BitVec.fromBEBytes, BitVec.toNat_cast]
  rw [BitVec.toBEBytes, List.map_reverse, List.map_reverse, List.reverse_reverse, List.map_map]
  change (BitVec.fromLEBytes (List.map id value.bv.toLEBytes)).toNat = _
  rw [List.map_id, BitVec.fromLEBytes_toLEBytes (by decide : 32 % 8 = 0)]
  rfl

theorem composition (value : U32) : endian_roundtrip value = RustM.ok value := by
  simp [endian_roundtrip, little_roundtrip, big_roundtrip]

theorem short_header (input : Slice U8) (short : input.val.length < 4) :
    read_header input = RustM.ok none := by
  simp [read_header, experiment_core.protocol.read_header, UScalar.lt_equiv, short]

theorem header_value (a b c d : U8) (tail : List U8)
    (bound : ([a, b, c, d] ++ tail).length ≤ Usize.max) :
    read_header (Slice.from ([a, b, c, d] ++ tail) bound) =
      RustM.ok (some (core.num.U32.from_be_bytes (Array.make 4#usize [a,b,c,d]))) := by
  simp [read_header, experiment_core.protocol.read_header, UScalar.lt_equiv,
    Slice.index_usize, lift]

-- An asymmetric wire value distinguishes big-endian decoding from little-endian.
theorem network_order :
    read_header (Slice.from [18#u8, 52#u8, 86#u8, 120#u8] (by scalar_tac)) =
      RustM.ok (some 305419896#u32) := by
  change read_header (Slice.from ([18#u8, 52#u8, 86#u8, 120#u8] ++ []) _) = _
  rw [header_value]
  rfl

end Endian.Properties
