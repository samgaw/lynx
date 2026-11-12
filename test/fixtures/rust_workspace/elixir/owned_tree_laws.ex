defmodule LynxRustFixture.OwnedTreeLaws do
  @compile :debug_info
  use Lynx.Laws

  def bytes?([]), do: true

  def bytes?([head | tail]),
    do: is_integer(head) and head >= 0 and head <= 255 and bytes?(tail)

  def bytes?(_), do: false

  law counts(input),
    requires: bytes?(input) and length(input) <= 65535,
    expects: LynxRustFixture.OwnedTreeNative.owned_tree_nodes(input, 2) == 2,
    proof: ~LEAN"""
    have decoded (input : Lynx.Term) (valid : «bytes?/1» input = .ok Lynx.Term.true) :
        ∃ (terms : List Lynx.Term) (values : List Aeneas.Std.U8),
          input = Lynx.Term.list terms ∧
          List.Forall₂ (fun term byte => Lynx.Rustler.decodeUnsigned .U8 32 term = .ok byte) terms values ∧
          Erlang.erlang.«length/1» input = .ok (.integer values.length) := by
      induction input using «bytes?/1».induct with
      | case1 => exact ⟨[], [], rfl, .nil, rfl⟩
      | case2 head tail ih =>
        cases head <;> simp [«bytes?/1», Erlang.erlang.«is_integer/1»] at valid
        rename_i number
        obtain ⟨terms, values, shape, paired, length⟩ := ih valid.2.2
        let byte : Aeneas.Std.U8 := ⟨BitVec.ofNat 8 number.toNat⟩
        have byteDecoded : Lynx.Rustler.decodeUnsigned .U8 32 (.integer number) = .ok byte := by
          simp [Lynx.Rustler.decodeUnsigned, byte, valid.1]
          omega
        refine ⟨.integer number :: terms, byte :: values, ?_, .cons byteDecoded paired, ?_⟩
        · simp [shape, Lynx.Term.list]
        · simp [Erlang.erlang.«length/1», length]
      | case3 input notNil notCons => simp_all [«bytes?/1»]
    cases computed : «bytes?/1» input with
    | error error => simp [«counts:requires/1», computed] at requires
    | ok result =>
      cases result <;> simp [«counts:requires/1», computed] at requires
      rename_i flag
      rcases requires with ⟨rfl, small⟩
      obtain ⟨terms, values, shape, paired, length⟩ := decoded input computed
      simp [length, Erlang.erlang.«=</2», Int.compare_eq_gt] at small
      have bounded : values.length ≤ 65535 := by omega
      have native : values.length ≤ Aeneas.Std.Usize.max ∧ values.length ≤ Aeneas.Std.Isize.max.toNat := by
        constructor <;> scalar_tac
      have decodedInput : Lynx.Rustler.decodeByteVec input =
          .ok (Aeneas.Std.alloc.vec.Vec.from values native.1) := by
        rw [shape]
        apply Lynx.Rustler.decodeByteVec_values paired (by simp [Lynx.Rustler.byteVecLimit]; omega) native
      simp [«counts:ensures/1», Elixir.LynxRustFixture.OwnedTreeNative.«owned_tree_nodes/2»,
        Elixir.LynxRustFixture.OwnedTreeNative.«owned_tree_nodes:execution/2», decodedInput,
        Lynx.Rustler.decodeUnsigned, Lynx.Rustler.execute, Lynx.Rustler.encodeOption,
        Lynx.Rustler.encodeUnsigned, OwnedTreeNative.NativeProperties.facade,
        Erlang.erlang.«==/2», Aeneas.Std.UScalar.val]
    """

  law too_small,
    expects: LynxRustFixture.OwnedTreeNative.owned_tree_nodes([0, 255], 1) == nil,
    proof: ~LEAN"""
    simp [«too_small:ensures/0», Elixir.LynxRustFixture.OwnedTreeNative.«owned_tree_nodes/2»,
      Elixir.LynxRustFixture.OwnedTreeNative.«owned_tree_nodes:execution/2»,
      OwnedTreeNative.NativeProperties.sample_decoded, OwnedTreeNative.NativeProperties.facade,
      Lynx.Rustler.decodeUnsigned, Lynx.Rustler.execute, Lynx.Rustler.encodeOption,
      Erlang.erlang.«==/2», Aeneas.Std.UScalar.val]
    """

  law wrapped_budget,
    expects: LynxRustFixture.OwnedTreeNative.owned_tree_nodes([0, 255], 65538) == 2,
    proof: ~LEAN"""
    simp [«wrapped_budget:ensures/0», Elixir.LynxRustFixture.OwnedTreeNative.«owned_tree_nodes/2»,
      Elixir.LynxRustFixture.OwnedTreeNative.«owned_tree_nodes:execution/2»,
      OwnedTreeNative.NativeProperties.sample_decoded, OwnedTreeNative.NativeProperties.facade,
      Lynx.Rustler.decodeUnsigned, Lynx.Rustler.execute, Lynx.Rustler.encodeOption,
      Lynx.Rustler.encodeUnsigned, Erlang.erlang.«==/2», Aeneas.Std.UScalar.val]
    """

  law rejects_nonlist,
    expects:
      (try do
         LynxRustFixture.OwnedTreeNative.owned_tree_nodes(42, 2)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [«rejects_nonlist:ensures/0», Elixir.LynxRustFixture.OwnedTreeNative.«owned_tree_nodes/2»,
      Lynx.Rustler.decodeByteVec_integer, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law improper_tail,
    expects:
      (try do
         LynxRustFixture.OwnedTreeNative.owned_tree_nodes([0 | 1], 2)
         false
       catch
         :error, :nif_panicked -> true
       end),
    proof: ~LEAN"""
    have rejected := Lynx.Rustler.decodeByteVec_improper (0#u8) 1
    change Lynx.Rustler.decodeByteVec (.cons (.integer 0) (.integer 1)) =
      .error (.error (.atom "nif_panicked")) at rejected
    simp [«improper_tail:ensures/0», Elixir.LynxRustFixture.OwnedTreeNative.«owned_tree_nodes/2»,
      rejected, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """
end
