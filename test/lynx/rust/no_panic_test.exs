defmodule Lynx.Rust.NoPanicTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.NoPanic

  test "requires checked runtime contracts with unambiguous identities" do
    assert :ok =
             NoPanic.validate!(
               execution: :runtime,
               nonpanicking: [{"core_lib::parse", "Proofs.safe"}]
             )

    for contracts <- [
          true,
          ["core_lib::parse"],
          [{"x", "Proofs.safe"}],
          [{"core_lib::parse", "Proofs.safe"}, {"core_lib::parse", "Proofs.other"}]
        ] do
      assert_raise ArgumentError, ~r/nonpanicking requires/, fn ->
        NoPanic.validate!(execution: :runtime, nonpanicking: contracts)
      end
    end

    assert_raise ArgumentError, ~r/runtime execution/, fn ->
      NoPanic.validate!(nonpanicking: [{"core_lib::parse", "Proofs.safe"}])
    end

    assert :ok =
             NoPanic.validate!(
               execution: :runtime,
               unwind: :captured,
               nonpanicking: [{"core_lib::parse", "Proofs.safe"}]
             )

    assert_raise ArgumentError, ~r/unwind: :reject or :captured/, fn ->
      NoPanic.validate!(
        execution: :runtime,
        unwind: :assertions,
        nonpanicking: [{"core_lib::parse", "Proofs.safe"}]
      )
    end
  end

  test "protects complete original direct-call bodies including recursive dependencies" do
    document =
      document([function(1, "parse", [2]), function(2, "step", [1, 3]), function(3, "leaf", [])])

    assert {^document,
            %{
              contracts: [%{id: 1, rust: "core_lib::parse", theorem: "Proofs.safe"}],
              protected: protected
            }} =
             NoPanic.prepare!(document, [{"core_lib::parse", "Proofs.safe"}], ["core_lib"])

    assert protected == MapSet.new([1, 2, 3])
  end

  test "protects actual constant initializers and their transitive callees" do
    reader =
      put_in(function(1, "parse", []), ["body", "Structured"], %{
        "place" => %{"Global" => %{"id" => 8}}
      })

    input = document([reader, function(2, "initializer", [3]), function(3, "leaf", [])])

    input =
      put_in(input, ["translated", "global_decls"], [
        %{
          "def_id" => 8,
          "value" => %{"Value" => [40, [%{"Call" => [%{"kind" => %{"Fun" => 2}}, []]}, %{}]]}
        }
      ])

    {_, plan} = NoPanic.prepare!(input, [{"core_lib::parse", "Proofs.safe"}], ["core_lib"])
    assert plan.protected == MapSet.new([1, 2, 3])
  end

  test "protects compiler dictionary methods and inherited dictionaries before cleanup pruning" do
    first =
      put_in(function(1, "parse", []), ["body", "Structured"], %{
        "trait_refs" => [
          %{
            "skip_binder" => %{
              "Value" => [
                20,
                %{
                  "kind" => %{"TraitImpl" => %{"id" => 7}},
                  "trait_decl_ref" => %{}
                }
              ]
            }
          }
        ]
      })

    input =
      document([
        first,
        function(2, "callback", [3]),
        function(3, "leaf", []),
        function(4, "inherited", []),
        function(5, "unrelated", [])
      ])

    input =
      put_in(input, ["translated", "trait_impls"], [
        %{
          "def_id" => 7,
          "methods" => [%{"skip_binder" => %{"id" => 2}}],
          "implied_trait_refs" => [%{"TraitImpl" => %{"id" => 8}}]
        },
        %{
          "def_id" => 8,
          "methods" => [%{"skip_binder" => %{"id" => 4}}],
          "implied_trait_refs" => [%{"TraitImpl" => %{"id" => 7}}]
        }
      ])

    {^input, plan} = NoPanic.prepare!(input, [{"core_lib::parse", "Proofs.safe"}], ["core_lib"])
    assert plan.protected == MapSet.new([1, 2, 3, 4])

    assert :ok =
             NoPanic.audit!(plan, %{
               functions: input["translated"]["fun_decls"],
               constants: %{},
               callback_dependencies: %{1 => [2, 4]}
             })
  end

  test "rejects a missing or opaque first-party implementation" do
    for functions <- [[], [put_in(function(1, "parse", []), ["body"], "Opaque")]] do
      assert_raise ArgumentError, ~r/extracted ordinary first-party/, fn ->
        NoPanic.prepare!(document(functions), [{"core_lib::parse", "Proofs.safe"}], ["core_lib"])
      end
    end
  end

  test "resolved callback dependencies cannot bypass original body protection" do
    first = function(1, "parse", [])
    hidden = function(2, "callback", [])

    {_, plan} =
      NoPanic.prepare!(document([first, hidden]), [{"core_lib::parse", "Proofs.safe"}], [
        "core_lib"
      ])

    audit = %{functions: [first, hidden], constants: %{}, callback_dependencies: %{1 => [2]}}

    assert_raise ArgumentError, ~r/indirect implementation dependencies/, fn ->
      NoPanic.audit!(plan, audit)
    end
  end

  test "links certificates to actual extracted function identities" do
    {_, plan} =
      NoPanic.prepare!(
        document([function(1, "parse", [])]),
        [{"core_lib::parse", "Proofs.safe"}],
        ["core_lib"]
      )

    assert [%{rust: "core_lib::parse", lean: "core_lib.parse", theorem: "Proofs.safe"}] =
             NoPanic.link!(plan, %{
               1 => %{"rust_name" => "core_lib::parse", "lean_name" => "core_lib.parse"}
             })

    assert_raise ArgumentError, ~r/identity mismatch/, fn ->
      NoPanic.link!(plan, %{
        1 => %{"rust_name" => "core_lib::other", "lean_name" => "core_lib.parse"}
      })
    end
  end

  defp document(functions), do: %{"translated" => %{"fun_decls" => functions}}

  defp function(id, name, calls) do
    %{
      "def_id" => id,
      "src" => "Normal",
      "item_meta" => %{"name" => [%{"Ident" => ["core_lib", 0]}, %{"Ident" => [name, 0]}]},
      "body" => %{
        "Structured" => %{
          "body" => %{
            "statements" =>
              Enum.map(calls, fn callee ->
                %{
                  "kind" => %{
                    "Call" => %{
                      "call" => %{"func" => %{"Regular" => %{"kind" => %{"Fun" => callee}}}}
                    }
                  }
                }
              end)
          }
        }
      }
    }
  end
end
