defmodule Lynx.Rust.StringSplitsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CallModels, LibraryHelpers, LLBC, StringSplits}
  @snapshot Path.expand("../../fixtures/rustler/string_splits.json", __DIR__)

  test "selects the actual checked body and models only the scoped borrowing primitive" do
    t = snapshot()
    checked = Enum.find(t["fun_decls"], &match?(%{"Structured" => _}, &1["body"]))
    primitive = Enum.find(t["fun_decls"], &(&1["body"] == "Opaque"))
    assert StringSplits.checked_body?(checked, t, %{})
    assert LibraryHelpers.selected?(checked, t)
    refute StringSplits.resolve(checked, t, %{})

    assert %{str_split_unchecked: true, string_slice_op: "splitUnchecked"} =
             StringSplits.resolve(primitive, t, %{})

    refute LibraryHelpers.selected?(primitive, t)

    assert "core::str::_::split_at_checked" in LibraryHelpers.includes(%{
             sysroot: %{path: "full"}
           })

    refute "core::str::_::split_at_checked" in LibraryHelpers.includes()
  end

  test "rejects changed signatures, shared-borrow lifetimes and standard representations" do
    t = snapshot()

    for f <- t["fun_decls"] do
      valid = fn changed, translated ->
        StringSplits.checked_body?(changed, translated, %{}) ||
          StringSplits.resolve(changed, translated, %{})
      end

      [input, offset] = CallModels.expand(f["signature"]["inputs"], %{})
      [region, str, _] = input["Ref"]

      for changed <- [
            put_in(f, ["signature", "abi"], "C"),
            put_in(f, ["signature", "is_variadic"], true),
            put_in(f, ["signature", "is_unsafe"], not f["signature"]["is_unsafe"]),
            put_in(f, ["signature", "inputs"], [%{"Ref" => [region, str, "Mut"]}, offset]),
            put_in(f, ["signature", "inputs"], [
              %{"Ref" => [%{"Var" => %{"Free" => 1}}, str, "Shared"]},
              offset
            ]),
            put_in(f, ["signature", "output"], %{"Scalar" => "Bool"}),
            put_in(f, ["generics", "trait_clauses"], [%{}]),
            put_in(f, ["item_meta", "name"], [])
          ] do
        refute valid.(changed, t)
      end

      for type <- t["type_decls"],
          type && type["src"] in [%{"Builtin" => "Str"}, %{"Builtin" => "Tuple"}] do
        altered =
          Map.update!(
            t,
            "type_decls",
            &Enum.map(&1, fn row ->
              if row == type, do: Map.put(row, "src", "Normal"), else: row
            end)
          )

        refute valid.(f, altered)
      end
    end
  end

  test "rejects an unchecked borrowing primitive called outside the standard checked helper" do
    t = snapshot()
    primitive = Enum.find(t["fun_decls"], &(&1["body"] == "Opaque"))

    call = %{
      "Call" => %{
        "call" => %{"func" => %{"Regular" => %{"kind" => %{"Fun" => primitive["def_id"]}}}}
      }
    }

    caller = %{
      "def_id" => 100,
      "src" => "Normal",
      "item_meta" => %{
        "name" => Enum.map(~w(first_party split), &%{"Ident" => [&1, 0]}),
        "opacity" => "Transparent"
      },
      "generics" => primitive["generics"],
      "signature" => Map.put(primitive["signature"], "is_unsafe", false),
      "body" => %{"Structured" => call}
    }

    t =
      Map.merge(t, %{
        "fun_decls" => [caller, primitive],
        "global_decls" => [],
        "trait_decls" => [],
        "trait_impls" => [],
        "files" => []
      })

    document = %{"charon_version" => "0.1.304", "has_errors" => false, "translated" => t}

    assert_raise CompileError, ~r/unchecked string splitting is restricted/, fn ->
      LLBC.audit!(document, ["first_party"])
    end
  end

  defp snapshot, do: JSON.decode!(File.read!(@snapshot))["translated"]
end
