module
public import BorrowedText.Extraction.Funs
public section
open Aeneas Aeneas.Std
namespace BorrowedText.Properties

theorem borrowed_echo (text : Str) : __CALLER__.borrowed_text text = .ok text := by
  rfl

theorem borrowed_header_composition (text : Str) :
    __CALLER__.borrowed_text_header text = __CORE__.read_header text := by
  exact bind_ok (α := Slice U8) text __CORE__.read_header

theorem borrowed_header_short (text : Str) (short : text.val.length < 4) :
    __CALLER__.borrowed_text_header text = .ok none := by
  rw [borrowed_header_composition]
  simp [__CORE__.read_header, UScalar.lt_equiv, short]

theorem borrowed_header_value (a b c d : U8) (tail : List U8)
    (bound : ([a,b,c,d] ++ tail).length ≤ Usize.max) :
    __CALLER__.borrowed_text_header (Slice.from ([a,b,c,d] ++ tail) bound) =
      .ok (some (core.num.U32.from_be_bytes (Array.make 4#usize [a,b,c,d]))) := by
  rw [borrowed_header_composition (Slice.from ([a,b,c,d] ++ tail) bound)]
  simp [__CORE__.read_header, UScalar.lt_equiv, Slice.index_usize, lift]

theorem borrowed_network_order :
    __CALLER__.borrowed_text_header (toStr "LYNX!") = .ok (some 1280921176#u32) := by
  have text : toStr "LYNX!" = (Slice.from ([76#u8,89#u8,78#u8,88#u8] ++ [33#u8]) (by scalar_tac) : Str) := by
    exact Slice.ext _ _ (by decide +kernel)
  rw [text, borrowed_header_value]
  rfl

end BorrowedText.Properties
