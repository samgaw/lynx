module
public import Tables.IterationProperties
public import Tables.RustlerBridge
public section
open Aeneas Aeneas.Std
unseal RustM
namespace Tables.AdapterProperties
 theorem preview_entries (firstKey firstValue secondKey secondValue : U64) :
    __ENTRIES_NIF__ firstKey firstValue secondKey secondValue =
      .ok (if firstKey.val = secondKey.val then (some secondKey, some secondValue, none, none, 1#u64)
        else if firstKey.val < secondKey.val then
          (some firstKey, some firstValue, some secondKey, some secondValue, 2#u64)
        else (some secondKey, some secondValue, some firstKey, some firstValue, 2#u64)) := by
  simpa [__ENTRIES_NIF__, lift] using Tables.Properties.preview_entries firstKey firstValue secondKey secondValue
 theorem preview_members (first second : U64) :
    __MEMBERS_NIF__ first second =
      .ok (if first.val = second.val then (some second, none, 1#u64)
        else if first.val < second.val then (some first, some second, 2#u64)
        else (some second, some first, 2#u64)) := by
  simpa [__MEMBERS_NIF__, lift] using Tables.Properties.preview_members first second
end Tables.AdapterProperties
