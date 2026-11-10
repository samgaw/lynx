defmodule Lynx.Rust.OwnershipUnwindTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{LLBC, OwnershipUnwind}
  @fixture Path.expand("../../fixtures/rust/explicit_ownership.json", __DIR__)

  test "does not discard destructor work or termination while propagating failure" do
    doc = @fixture |> File.read!() |> JSON.decode!()
    audit = LLBC.audit!(doc, ["lynx_explicit_scalar"], explicit_ownership: true)
    consumer = Enum.find(audit.functions, &(&1["def_id"] == 19))
    OwnershipUnwind.audit!([consumer], audit.translated, audit.references)

    for kind <- ["UnwindTerminate", %{"Assign" => [nil, nil]}, %{"Call" => %{}}] do
      changed =
        update_in(consumer, ["body", "Structured", "body"], fn body ->
          replace_cleanup(body, kind)
        end)

      assert_raise CompileError, ~r/observable unwind cleanup/, fn ->
        OwnershipUnwind.audit!([changed], audit.translated, audit.references)
      end
    end
  end

  test "fallible operations cannot lose cleanup edges while a generic owner exists" do
    doc = @fixture |> File.read!() |> JSON.decode!()
    audit = LLBC.audit!(doc, ["lynx_explicit_scalar"], explicit_ownership: true)
    consumer = Enum.find(audit.functions, &(&1["def_id"] == 19))

    changed =
      update_in(consumer, ["body", "Structured", "body", "statements"], fn statements ->
        [%{"kind" => %{"Assign" => [nil, %{"BinaryOp" => ["Add", nil, nil]}]}} | statements]
      end)

    assert_raise CompileError, ~r/reconstructed fallible operations with owned locals/, fn ->
      OwnershipUnwind.audit!([changed], audit.translated, audit.references)
    end
  end

  test "reconstructed assertions cannot certify erased owner cleanup as empty" do
    doc = @fixture |> File.read!() |> JSON.decode!()
    audit = LLBC.audit!(doc, ["lynx_explicit_scalar"], explicit_ownership: true)
    consumer = Enum.find(audit.functions, &(&1["def_id"] == 19))

    changed =
      update_in(consumer, ["body", "Structured", "body", "statements"], fn statements ->
        [
          %{
            "kind" => %{
              "Assert" => %{
                "assert" => %{"cond" => nil, "expected" => true, "check_kind" => nil},
                "on_failure" => %{"Panic" => []},
                "on_unwind" => %{"statements" => [%{"kind" => "UnwindResume"}]}
              }
            }
          }
          | statements
        ]
      end)

    assert_raise CompileError, ~r/reconstructed assertions with owned locals/, fn ->
      OwnershipUnwind.audit!([changed], audit.translated, audit.references)
    end
  end

  defp replace_cleanup(%{"on_unwind" => cleanup} = node, kind),
    do: %{
      node
      | "on_unwind" => %{
          cleanup
          | "statements" => [%{"kind" => kind}, %{"kind" => "UnwindResume"}]
        }
    }

  defp replace_cleanup(map, kind) when is_map(map),
    do: Map.new(map, fn {key, value} -> {key, replace_cleanup(value, kind)} end)

  defp replace_cleanup(list, kind) when is_list(list),
    do: Enum.map(list, &replace_cleanup(&1, kind))

  defp replace_cleanup(value, _), do: value
end
