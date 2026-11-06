defmodule Lynx.Rust.FuturesTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.Futures

  test "keeps immediate future extraction in pure execution mode" do
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

  @tag :tmp_dir
  test "suspension requires both compiler storage and backend cutoff capabilities", %{
    tmp_dir: tmp
  } do
    immediate = "charon=base+immediate-futures-v1\naeneas=base+immediate-futures-v1\n"

    for manifest <- [
          immediate,
          String.replace(immediate, "charon=base", "charon=base+suspending-futures-v1"),
          String.replace(immediate, "aeneas=base", "aeneas=base+undefined-behavior-v1")
        ] do
      File.write!(Path.join(tmp, "lynx-toolchain"), manifest)

      assert_raise ArgumentError, ~r/suspending-futures-v1 and undefined-behavior-v1/, fn ->
        Futures.arguments!(:suspending, tmp)
      end
    end

    File.write!(
      Path.join(tmp, "lynx-toolchain"),
      "charon=base+immediate-futures-v1+suspending-futures-v1\naeneas=base+immediate-futures-v1+undefined-behavior-v1\n"
    )

    assert "--suspending-futures" in Futures.arguments!(:suspending, tmp)
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

  @tag :tmp_dir
  test "cancellation requires its compiler capability and optimized drop MIR", %{tmp_dir: tmp} do
    manifest =
      "charon=base+immediate-futures-v1+suspending-futures-v1\naeneas=base+immediate-futures-v1+undefined-behavior-v1\n"

    path = Path.join(tmp, "lynx-toolchain")
    File.write!(path, manifest)

    assert_raise ArgumentError, ~r/cancelling-futures-v1/, fn ->
      Futures.arguments!(:cancelling, tmp)
    end

    File.write!(
      path,
      String.replace(manifest, "charon=base", "charon=base+cancelling-futures-v1")
    )

    assert ["--cancelling-futures", "--mir", "optimized", "--suspending-futures" | _] =
             Futures.arguments!(:cancelling, tmp)

    assert_raise ArgumentError, ~r/requires runtime execution/, fn ->
      Lynx.Rust.Extraction.run!(%{}, "/unused", ["probe::future"], "/unused", "Probe.Extraction",
        futures: :cancelling,
        execution: :pure
      )
    end
  end
end
