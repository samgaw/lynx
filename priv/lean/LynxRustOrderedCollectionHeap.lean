module
public import __RUNTIME__
public import __PREFIX__.OrderedCollectionsModel
public section
open Aeneas Aeneas.Std
namespace __PREFIX__.OrderedCollectionHeap
open __PREFIX__.OrderedCollections

theorem map_rebuild (table : Map) : Std.ExtTreeMap.ofList table.toList = table := by
  apply Std.ExtTreeMap.ext_getElem?
  intro key
  cases found : table[key]? with
  | none =>
    apply Std.ExtTreeMap.getElem?_ofList_of_contains_eq_false
    have absent : key ∉ table := by rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, found]; simp
    simpa using absent
  | some value =>
    apply Std.ExtTreeMap.getElem?_ofList_of_mem (k := key) (k' := key) (by simp)
      table.distinct_keys_toList
    exact Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr found

theorem set_rebuild (values : Set) : Std.ExtTreeSet.ofList values.toList = values := by
  apply Std.ExtTreeSet.ext_mem
  intro key
  simp

@[expose] def encodeRows : List (Nat × U64) → Lynx.Term
  | [] => .nil
  | (key, value) :: tail => .cons (.cons (.integer key) (Lynx.NativeCodec.encode value)) (encodeRows tail)
@[expose] def decodeRows : Lynx.Term → Option (List (Nat × U64))
  | .nil => some []
  | .cons (.cons (.integer key) encoded) tail => do
    if key < 0 then none else do
      let value ← Lynx.NativeCodec.decode encoded
      let rest ← decodeRows tail
      return (key.toNat, value) :: rest
  | _ => none

theorem rows_roundtrip (rows : List (Nat × U64)) : decodeRows (encodeRows rows) = some rows := by
  induction rows with
  | nil => rfl
  | cons row tail ih => cases row; simp [encodeRows, decodeRows, Lynx.NativeCodec.roundtrip, ih]

instance : Lynx.NativeCodec Map where
  typeName := "alloc::collections::BTreeMap<u64,u64>:ordered-v1"
  encode value := encodeRows value.toList
  decode term := (decodeRows term).map (fun rows => (Std.ExtTreeMap.ofList rows : Map))
  decode_encode value := by simp [rows_roundtrip, map_rebuild]
@[expose] def encodeKeys : List Nat → Lynx.Term
  | [] => .nil
  | key :: tail => .cons (.integer key) (encodeKeys tail)
@[expose] def decodeKeys : Lynx.Term → Option (List Nat)
  | .nil => some []
  | .cons (.integer key) tail => do
    if key < 0 then none else do
      let rest ← decodeKeys tail
      return key.toNat :: rest
  | _ => none

theorem keys_roundtrip (keys : List Nat) : decodeKeys (encodeKeys keys) = some keys := by
  induction keys with
  | nil => rfl
  | cons key tail ih => simp [encodeKeys, decodeKeys, ih]

instance : Lynx.NativeCodec Set where
  typeName := "alloc::collections::BTreeSet<u64>:ordered-v1"
  encode values := encodeKeys values.toList
  decode term := (decodeKeys term).map (fun keys => (Std.ExtTreeSet.ofList keys : Set))
  decode_encode values := by simp [keys_roundtrip, set_rebuild]
end __PREFIX__.OrderedCollectionHeap
