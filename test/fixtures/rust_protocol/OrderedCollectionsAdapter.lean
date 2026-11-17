module
public import Tables.Properties
public import Tables.RustlerBridge
public section
open Aeneas Aeneas.Std
unseal RustM
namespace Tables.AdapterProperties
 theorem replace (key value replacement : U64) :
    __REPLACE_NIF__ key value replacement = .ok (some value) := by
  simpa [__REPLACE_NIF__, lift] using Tables.Properties.replace key value replacement
 theorem duplicate (key : U64) :
    __CLAIMS_NIF__ key = .ok (true, false, 1#u64) := by
  simpa [__CLAIMS_NIF__, lift] using Tables.Properties.duplicate key
 theorem stats (firstKey firstValue secondKey secondValue : U64) :
    __STATS_NIF__ firstKey firstValue secondKey secondValue =
      .ok (if firstKey.val = secondKey.val then (some firstValue, 1#u64) else (none, 2#u64)) := by
  simpa [__STATS_NIF__, lift] using Tables.Properties.stats firstKey firstValue secondKey secondValue
theorem take_once (key value query : U64) :
    __TAKE_NIF__ key value query =
      .ok (if key.val = query.val then (some value, some value, none, 0#u64)
        else (none, none, none, 1#u64)) := by
  simpa [__TAKE_NIF__, lift] using Tables.Properties.take_once key value query

theorem release_once (key query : U64) :
    __RELEASE_NIF__ key query =
      .ok (if key.val = query.val then (true, true, false, false, 0#u64)
        else (false, false, false, false, 1#u64)) := by
  simpa [__RELEASE_NIF__, lift] using Tables.Properties.release_once key query
end Tables.AdapterProperties
