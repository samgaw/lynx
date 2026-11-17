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
end Tables.AdapterProperties
