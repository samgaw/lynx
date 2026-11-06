defmodule Lynx.Rust.ReportTest do
  use ExUnit.Case, async: true

  test "reports cross-crate implementations through recursive same-crate wrappers" do
    names = %{0 => "facade::caller", 1 => "facade::wrapper", 2 => "algorithm::update"}

    models =
      Map.new(names, fn {id, name} ->
        {id, %{"def_id" => id, "rust_name" => name, "lean_name" => "Extracted.f#{id}"}}
      end)

    # Reporting consumes the already audited graph. The native integration
    # separately checks extraction, theorem elaboration and complete proof audits.
    edges = %{0 => [1], 1 => [0, 2, 3], 2 => [1], 3 => []}

    extraction = %{
      implementations: models,
      fingerprint: "report-fixture",
      audit: %{
        functions: Enum.map(edges, fn {id, _} -> %{"def_id" => id, "body" => nil} end),
        callback_dependencies: edges,
        constants: %{},
        external_calls: %{
          3 => %{
            definition_id: 3,
            rust_name: "external::operation",
            label: "External model",
            implementation_verified: false
          }
        },
        library_helpers: [],
        drops: %{sites: %{}, erasures: %{}},
        translated: %{"type_decls" => []}
      }
    }

    properties = [
      %{
        "theorem" => "Proof.caller",
        "statement" => "Extracted.f0 satisfies its property",
        "implementations" => ["Extracted.f0"],
        "contracts_used" => []
      }
    ]

    reports = [
      %{
        status: :ok,
        module: "Proof",
        diagnostics: [
          %{severity: :information, message: "LYNX_RUST_PROPERTIES:" <> JSON.encode!(properties)}
        ]
      }
    ]

    result = Lynx.Rust.Report.build!(extraction, reports, source_dir: __DIR__)

    assert [
             %{kind: :rust_implementation, implementation_dependencies: [%{"def_id" => 1}]},
             %{
               kind: :cross_crate_contract,
               theorem: "Proof.caller",
               implementation_dependencies: [
                 %{
                   "def_id" => 2,
                   "rust_name" => "algorithm::update",
                   "lean_name" => "Extracted.f2"
                 }
               ]
             }
           ] = result.guarantees

    assert [%{definition_id: 3, implementation_verified: false}] =
             result.unverified_external_calls
  end
end
