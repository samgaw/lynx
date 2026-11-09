defmodule Lynx.Rust.OptionModels do
  @moduledoc false
  alias Lynx.Rust.CallModels

  # Only Some transfers a value. None cannot establish a Rust outcome until
  # panic formatting, hooks and unwind are supported for this standard call.
  def resolve(function, translated, refs) do
    with %{
           "body" => "Opaque",
           "src" => "Normal",
           "signature" => %{"abi" => "Rust", "is_unsafe" => false, "is_variadic" => false} = sig,
           "item_meta" => %{
             "name" => [
               %{"Ident" => ["core", 0]},
               %{"Ident" => ["option", 0]},
               %{
                 "Impl" => %{
                   "Ty" => %{
                     "kind" => "InherentImplBlock",
                     "params" => parent_params,
                     "skip_binder" => parent
                   }
                 }
               },
               %{"Ident" => ["expect", 0]}
             ]
           },
           "generics" => params
         } <- function,
         true <- parameters?(parent_params, 0),
         true <- parameters?(params, 1),
         [input, %{"Ref" => [%{"Var" => %{"Free" => 0}}, string, "Shared"]}] <-
           CallModels.expand(sig["inputs"], refs),
         %{"Adt" => %{"builtin" => "Str", "generics" => str_args}} <- string,
         true <- str_args == arguments([]),
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}} <- input,
         true <- args == arguments([variable()]),
         true <-
           CallModels.expand(parent, refs) ==
             put_in(input, ["Adt", "generics", "types"], [%{"TypeVar" => %{"Bound" => [0, 0]}}]),
         true <- CallModels.expand(sig["output"], refs) == variable(),
         type when not is_nil(type) <-
           Enum.find(translated["type_decls"], &(&1 && &1["def_id"] == id)),
         true <- option?(type, refs) do
      %{
        rust_name: "core::option::{core::option::Option<@T>}::expect",
        lean: "Lynx.NativeM.expectSome",
        backend_rust_name: "lynx_native::option_expect_some",
        native_expect_some: true,
        builtin: false,
        can_fail: true,
        lift: true,
        native_transfer: true,
        native_cutoff_only: true,
        label:
          "Native Option::expect successful-Some model with exact Option layout and signature validation; None panic formatting, hooks and unwind exhaust verification; Rust core implementation not verified"
      }
    else
      _ -> nil
    end
  end

  defp option?(type, refs) do
    type["item_meta"]["name"] == Enum.map(~w(core option Option), &%{"Ident" => [&1, 0]}) and
      parameters?(type["generics"], 0) and
      match?(
        %{
          "Enum" => [
            %{
              "id" => 0,
              "name" => "None",
              "fields" => [],
              "discriminant" => %{"Signed" => ["Isize", "0"]}
            },
            %{
              "id" => 1,
              "name" => "Some",
              "fields" => [%{"ty" => %{"TypeVar" => %{"Free" => 0}}}],
              "discriminant" => %{"Signed" => ["Isize", "1"]}
            }
          ]
        },
        CallModels.expand(type["kind"], refs)
      )
  end

  defp parameters?(
         %{
           "regions" => regions,
           "types" => [%{"index" => 0}],
           "const_generics" => [],
           "trait_clauses" => [],
           "outlives" => [],
           "trait_type_constraints" => []
         },
         count
       ) do
    case {count, regions} do
      {0, []} -> true
      {1, [%{"index" => 0}]} -> true
      _ -> false
    end
  end

  defp parameters?(_, _), do: false

  defp variable, do: %{"TypeVar" => %{"Free" => 0}}

  defp arguments(types),
    do: %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}
end
