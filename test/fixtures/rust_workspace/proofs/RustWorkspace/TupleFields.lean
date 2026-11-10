module
public import TupleFields.Extraction.Funs
public import TupleFields.RustlerBridge
public section
open Aeneas Aeneas.Std
namespace TupleFields.Properties

theorem fields_spec (fields : Array Lynx.Term)
    (bounds : fields.toList.length ≤ Usize.max ∧ fields.toList.length ≤ Isize.max.toNat ∧
      fields.toList.length ≤ 16777215) :
    experiment_nif.tuple_fields (.tuple fields) =
      RustM.ok (.Ok (alloc.vec.Vec.from fields.toList bounds.1)) := by
  simpa [experiment_nif.tuple_fields] using Lynx.Rustler.Decoding.getTuple_fields fields bounds

theorem rejected_spec (input : Lynx.Term) (notTuple : ∀ fields, input ≠ .tuple fields) :
    experiment_nif.tuple_fields input = RustM.ok (.Err Lynx.Rustler.badArgOutcome) := by
  simpa [experiment_nif.tuple_fields] using Lynx.Rustler.Decoding.getTuple_not_tuple input notTuple

theorem oversized_spec (fields : Array Lynx.Term)
    (outside : ¬ (fields.toList.length ≤ Usize.max ∧ fields.toList.length ≤ Isize.max.toNat ∧
      fields.toList.length ≤ 16777215)) :
    experiment_nif.tuple_fields (.tuple fields) = RustM.fail .undef := by
  simpa [experiment_nif.tuple_fields] using Lynx.Rustler.Decoding.getTuple_exhausted fields outside

end TupleFields.Properties
