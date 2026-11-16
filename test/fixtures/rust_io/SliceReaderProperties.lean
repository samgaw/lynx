module
public import SliceReader.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace SliceReader.Properties
@[expose] def empty : Slice U8 := .from [] (by scalar_tac)
@[expose] def one : Slice U8 := .from [7#u8] (by scalar_tac)
@[expose] def input : Slice U8 := .from [7#u8,8#u8,9#u8] (by scalar_tac)
@[expose] def output : Slice U8 := .from [40#u8,41#u8] (by scalar_tac)
@[expose] def suffix : Slice U8 := .from [9#u8] (by scalar_tac)
@[expose] def eofError : NativeIoError := .staticMessage "UnexpectedEof"
  (NativeFile.bytes (toStr "failed to fill whole buffer"))

theorem core_word : io_core.slice_word input = Result.ok (.Ok 2055#u16,suffix) := by cbv

theorem composed_word : parse_slice input = Result.ok (.Ok (2055#u16,1#usize),suffix) := by
  simp only [parse_slice,monadLift_self,core_word,Result.ok_bind]
  cbv

theorem empty_read : io_core.fill_slice input empty = Result.ok (.Ok (),input,empty) := by cbv

theorem one_read : io_core.fill_slice input one = Result.ok
    (.Ok (),Slice.from [8#u8,9#u8] (by scalar_tac),one) := by cbv

/-- This standard implementation consumes short input without copying its prefix. -/
theorem short_read : io_core.fill_slice one output = Result.ok (.Err eofError,empty,output) := by cbv

theorem empty_word : io_core.slice_word empty = Result.ok (.Err eofError,empty) := by cbv
theorem suffix_valid (input : Slice U8) (start : Usize) (valid : start.val ≤ input.length) :
    io_core.slice_suffix input start = Result.ok (input.drop start) := by
  simp [io_core.slice_suffix,core.slice.index.Slice.index,SliceReader.Extraction.SliceModel.rangeFrom,
    SliceReader.Extraction.SliceModel.indexFrom_valid,valid,NativeM.monadLift_eq,NativeM.fromRust_ok]

theorem suffix_invalid (input : Slice U8) (start : Usize) (invalid : ¬start.val ≤ input.length) :
    io_core.slice_suffix input start = NativeM.fail .panic := by
  simp [io_core.slice_suffix,core.slice.index.Slice.index,SliceReader.Extraction.SliceModel.rangeFrom,
    SliceReader.Extraction.SliceModel.indexFrom_invalid,invalid,NativeM.monadLift_eq,NativeM.fromRust]
theorem eof_constant : core.io.error.Error.READ_EXACT_EOF = Result.ok eofError := by
  simp [core.io.error.Error.READ_EXACT_EOF,SliceReader.Extraction.IoErrorModel.fromStaticMessage,
    SliceReader.Extraction.IoErrorModel.encodeKind,core.hint.must_use,NativeM.ok,eofError]

theorem fill_short (source destination : Slice U8) (short : source.length < destination.length) :
    io_core.fill_slice source destination = Result.ok (.Err eofError,empty,destination) := by
  have less : Slice.len destination > Slice.len source := by simpa using short
  have empty_suffix : source.drop (Slice.len source) = empty := by
    apply Slice.ext
    simp [empty,Slice.drop]
  simp [io_core.fill_slice,Shared0SliceU8.Insts.AllocIoReadRead.read_exact,less,
    core.slice.index.Slice.index,SliceReader.Extraction.SliceModel.rangeFrom,
    SliceReader.Extraction.SliceModel.indexFrom_valid,empty_suffix,eof_constant,
    NativeM.monadLift_eq,NativeM.fromRust_ok,NativeM.ok]
end SliceReader.Properties
