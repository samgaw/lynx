defmodule Lynx.Rust.FuturesTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.Futures

  test "rejects runtime future interpretation until effectful polling is supported" do
    assert_raise ArgumentError, ~r/requires pure execution/, fn ->
      Lynx.Rust.Extraction.run!(%{}, "/unused", ["probe::future"], "/unused", "Probe.Extraction",
        futures: :immediate,
        execution: :runtime
      )
    end
  end

  @tag :tmp_dir
  test "requires the compiler extension and rejects unknown future modes", %{tmp_dir: tmp} do
    File.write!(Path.join(tmp, "lynx-toolchain"), "charon=needs-drop-v1\n")
    assert Futures.arguments!(:reject, tmp) == []

    assert_raise ArgumentError, ~r/immediate-futures-v1/, fn ->
      Futures.arguments!(:immediate, tmp)
    end

    assert_raise ArgumentError, ~r/unsupported Rust future/, fn ->
      Futures.arguments!(:all, tmp)
    end
  end

  test "admits only the compiler Context shape as an explicit unobserved type model" do
    context = %{
      "src" => "Normal",
      "kind" => "Opaque",
      "item_meta" => %{"name" => Enum.map(~w(core task wake Context), &%{"Ident" => [&1, 0]})},
      "generics" => %{"types" => [], "const_generics" => [], "regions" => [%{"index" => 0}]}
    }

    document = %{"translated" => %{"type_decls" => [nil, context]}}

    assert [%{rust: "core::task::wake::Context", lean: "Unit", import: "Aeneas"}] =
             Enum.map(
               Futures.type_models!(:immediate, document),
               &Map.take(&1, [:rust, :lean, :import])
             )

    for invalid <- [
          put_in(context, ["generics", "types"], [%{}]),
          Map.put(context, "kind", %{"Struct" => []})
        ] do
      assert_raise ArgumentError, ~r/compiler task Context definition/, fn ->
        Futures.type_models!(
          :immediate,
          put_in(document, ["translated", "type_decls"], [invalid])
        )
      end
    end
  end
end
