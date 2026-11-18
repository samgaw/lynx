defmodule Lynx.Rust.UnwindInputTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.NativeUnwind

  defp document do
    %{
      "translated" => %{
        "options" => %{
          "preset" => nil,
          "lift_associated_types" => ["*"],
          "treat_box_as_builtin" => true,
          "ops_to_function_calls" => true,
          "index_to_function_calls" => true,
          "reconstruct_panic_calls" => true,
          "reconstruct_matches" => true,
          "hide_marker_traits" => true,
          "hide_allocator" => true,
          "remove_unused_self_clauses" => true,
          "remove_adt_clauses" => true,
          "unbind_item_vars" => true,
          "deallocate_all_locals" => true,
          "no_gen_tuple_structs" => true,
          "reconstruct_asserts" => false,
          "reconstruct_fallible_operations" => false,
          "no_typecheck" => false,
          "no_normalize" => false,
          "inline_anon_consts" => false,
          "desugar_drops" => false
        },
        "fun_decls" => [%{"body" => %{"Structured" => %{"cleanup" => "retained"}}}]
      }
    }
  end

  test "normalizes only the admission label and retains an auditable option record" do
    original = document()
    {normalized, record} = NativeUnwind.input!(original, :assertions)
    assert put_in(normalized, ["translated", "options", "preset"], nil) == original
    assert normalized["translated"]["options"]["preset"] == "Aeneas"
    assert :ok = NativeUnwind.validate_input!(original, :assertions, record)

    for invalid <- [nil, %{record | backend_preset: "other"}, %{record | options: %{}}] do
      assert_raise ArgumentError, ~r/input does not match/, fn ->
        NativeUnwind.validate_input!(original, :assertions, invalid)
      end
    end

    assert_raise ArgumentError, ~r/input does not match/, fn ->
      NativeUnwind.validate_input!(original, :reject, record)
    end
  end

  test "rejects missing and inconsistent extraction flags before admission" do
    original = document()

    for {key, value} <- original["translated"]["options"], replacement <- [:missing, !value] do
      changed =
        update_in(original, ["translated", "options"], fn options ->
          if replacement == :missing,
            do: Map.delete(options, key),
            else: Map.put(options, key, replacement)
        end)

      assert_raise ArgumentError, ~r/invalid assertion unwind extraction options/, fn ->
        NativeUnwind.input!(changed, :assertions)
      end
    end
  end

  test "captured unwind admits both supported drop modes with assertion resugaring disabled" do
    for explicit <- [false, true] do
      original =
        update_in(document(), ["translated", "options"], fn options ->
          %{options | "reconstruct_fallible_operations" => true, "desugar_drops" => explicit}
          |> Map.put("precise_drops", explicit)
        end)

      assert {normalized, %{kind: :validated_captured_options} = record} =
               NativeUnwind.input!(original, :captured)

      assert put_in(normalized, ["translated", "options", "preset"], nil) == original
      assert :ok = NativeUnwind.validate_input!(original, :captured, record)

      for {option, invalid} <- [
            {"reconstruct_asserts", true},
            {"reconstruct_fallible_operations", false},
            {"precise_drops", !explicit},
            {"preset", "Aeneas"}
          ] do
        changed = put_in(original, ["translated", "options", option], invalid)

        assert_raise ArgumentError, ~r/invalid captured unwind extraction options/, fn ->
          NativeUnwind.input!(changed, :captured)
        end
      end
    end
  end

  test "ordinary extraction keeps the original options" do
    original = document()
    assert {^original, nil} = NativeUnwind.input!(original, :reject)
  end
end
