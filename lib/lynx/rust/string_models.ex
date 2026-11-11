defmodule Lynx.Rust.StringModels do
  @moduledoc false
  alias Lynx.Rust.CallModels

  # Str is Aeneas's existing Slice U8 representation. These models preserve its
  # bytes and borrow; they do not prove Rust core's transmute or native layout.
  def resolve(function, translated, refs) do
    with %{
           "body" => "Opaque",
           "src" => "Normal",
           "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig,
           "generics" => params,
           "item_meta" => %{
             "name" => [
               %{"Ident" => ["core", 0]},
               %{"Ident" => ["str", 0]},
               %{
                 "Impl" => %{
                   "Ty" => %{
                     "kind" => "InherentImplBlock",
                     "params" => parent_params,
                     "skip_binder" => parent
                   }
                 }
               },
               %{"Ident" => [method, 0]}
             ]
           }
         } <- function,
         true <- method in ~w(as_bytes len is_empty),
         true <- parent_params == empty_params(),
         true <- match?([%{"index" => 0}], params["regions"]),
         true <- Map.put(params, "regions", []) == empty_params(),
         %{"Adt" => %{"id" => id, "builtin" => "Str", "generics" => args}} = str <-
           CallModels.expand(parent, refs),
         true <- args == arguments(),
         %{
           "src" => %{"Builtin" => "Str"},
           "generics" => type_params,
           "item_meta" => %{"name" => [%{"Builtin" => ["Str", 0]}]},
           "kind" => %{"Struct" => [%{"name" => "_0", "ty" => field}]}
         } <- Enum.find(translated["type_decls"], &(&1 && &1["def_id"] == id)),
         true <- type_params == empty_params(),
         true <- CallModels.expand(field, refs) == bytes(),
         true <- CallModels.expand(sig["inputs"], refs) == [reference(str)] do
      {output, lean, monadic} =
        case method do
          "as_bytes" -> {reference(bytes()), "id", false}
          "len" -> {scalar("Usize"), "Aeneas.Std.Slice.len", false}
          "is_empty" -> {%{"Scalar" => "Bool"}, "Aeneas.Std.core.slice.Slice.is_empty", true}
        end

      if CallModels.expand(sig["output"], refs) == output do
        %{
          rust_name: "core::str::{str}::" <> method,
          lean: lean,
          builtin: false,
          can_fail: monadic,
          lift: monadic,
          label:
            "Rust shared str byte-view model using Aeneas Slice U8; preserves bytes and byte length; Rust core/native layout not verified"
        }
      end
    else
      _ -> nil
    end
  end

  defp reference(type), do: %{"Ref" => [%{"Var" => %{"Free" => 0}}, type, "Shared"]}
  defp bytes, do: %{"Slice" => [scalar("U8"), nil]}
  defp scalar(type), do: %{"Scalar" => %{"Integer" => %{"Unsigned" => type}}}

  defp arguments,
    do: %{"regions" => [], "types" => [], "const_generics" => [], "trait_refs" => []}

  defp empty_params,
    do:
      Map.new(
        ~w(regions types const_generics trait_clauses outlives trait_type_constraints),
        &{&1, []}
      )
end
