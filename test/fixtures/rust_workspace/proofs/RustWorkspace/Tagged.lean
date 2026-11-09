module
public import Tagged.Extraction.Funs
public import Tagged.RustlerBridge
public section
open Aeneas Aeneas.Std experiment_nif
namespace Tagged.Properties

theorem core_spec (left right : U64) :
    experiment_core.order_pair left right =
      RustM.ok (if left ≤ right then (left, right) else (right, left)) := by
  unfold experiment_core.order_pair
  split <;> rfl

theorem caller_spec (left right : U64) :
    experiment_analysis.order_pair left right =
      RustM.ok (if left ≤ right then (left, right) else (right, left)) := core_spec left right

@[expose] def response (left right : U64) : OrderedReply :=
  if left = 0#u64 ∧ right = 0#u64 then .Empty
  else if left = right then .Equal left
  else if left ≤ right then .Ordered left right else .Ordered right left

theorem facade_spec (left right : U64) :
    __TAGGED_IMPLEMENTATION__ left right = RustM.ok (response left right) := by
  by_cases lz : left = 0#u64 <;> by_cases rz : right = 0#u64 <;>
    by_cases equal : left = right <;> by_cases ordered : left ≤ right <;>
    simp_all [__TAGGED_IMPLEMENTATION__, response, caller_spec]
  all_goals split <;> simp_all

@[expose] def replyTerm : OrderedReply → Lynx.Term
  | .Empty => .atom "empty"
  | .Equal value => .tuple #[.atom "equal", .integer value.val]
  | .Ordered left right => .tuple #[.atom "ordered", .integer left.val, .integer right.val]

theorem encoder_spec (value : OrderedReply) (env : Lynx.Rustler.Env) :
    OrderedReply.Insts.RustlerTypesEncoder.encode value env = RustM.ok (replyTerm value) := by
  cases value <;> simp [OrderedReply.Insts.RustlerTypesEncoder.encode, replyTerm,
    rustler_atoms_ordered_reply.atom_empty, rustler_atoms_ordered_reply.atom_equal,
    rustler_atoms_ordered_reply.atom_ordered, Tagged.Extraction.RustlerAtomCache.cache_0,
    Lynx.Rustler.Encoding.atom, Lynx.Rustler.Encoding.pair, Lynx.Rustler.Encoding.triple,
    Lynx.Rustler.Encoding.shared, Lynx.Rustler.Encoding.u64]

theorem encoded_facade (left right : U64) (env : Lynx.Rustler.Env) :
    (do
      let value ← __TAGGED_IMPLEMENTATION__ left right
      OrderedReply.Insts.RustlerTypesEncoder.encode value env) =
        RustM.ok (replyTerm (response left right)) := by
  simp [facade_spec, encoder_spec]

end Tagged.Properties
