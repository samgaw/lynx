module
public import Protocol.Extraction.BytesModel
public section
namespace Protocol.Cases
open Protocol.Extraction.Bytes

/-- Overlong encodings, surrogate code points, out-of-range code points,
truncated sequences and invalid continuations retain Rust's error details. -/
theorem errors :
    errorOffset 2 [255] 0 = some (0, some 1) ∧
    errorOffset 3 [65, 194] 0 = some (1, none) ∧
    errorOffset 4 [224, 128, 128] 0 = some (0, some 1) ∧
    errorOffset 4 [237, 160, 128] 0 = some (0, some 1) ∧
    errorOffset 5 [240, 144, 128, 65] 0 = some (0, some 3) ∧
    errorOffset 5 [244, 144, 128, 128] 0 = some (0, some 1) ∧
    errorOffset 4 [65, 226, 130] 0 = some (1, none) ∧
    errorOffset 5 [65, 226, 130, 65] 0 = some (1, some 2) := by
  decide +kernel

theorem valid_sequences :
    errorOffset 3 [195, 169] 0 = none ∧
    errorOffset 4 [226, 130, 172] 0 = none ∧
    errorOffset 5 [240, 159, 152, 128] 0 = none ∧
    errorOffset 4 [65, 0, 90] 0 = none := by
  decide +kernel

end Protocol.Cases
