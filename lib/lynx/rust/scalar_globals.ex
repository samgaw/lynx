defmodule Lynx.Rust.ScalarGlobals do
  @moduledoc false
  alias Lynx.Rust.{CallModels, Constants}

  # Reuse Aeneas's existing primitive MIN/MAX/BITS models. These are explicitly
  # reported standard-library models, never verified initializer implementations.
  def models(translated, refs) do
    models =
      for global <- translated["global_decls"],
          global != nil,
          model = resolve(global, translated["fun_decls"], refs),
          model != nil,
          do: {global["def_id"], Map.put(global, "lynx_scalar_model", model)}

    result = Map.new(models)

    if map_size(result) != length(models),
      do: raise(ArgumentError, "duplicate LLBC scalar constant identity")

    result
  end

  def resolve(global, functions, refs) do
    with %{
           "src" => "Normal",
           "global_kind" => "NamedConst",
           "generics" => params,
           "item_meta" => %{
             "opacity" => "Opaque",
             "name" => [
               %{"Ident" => ["core", 0]},
               %{"Ident" => ["num", 0]},
               %{
                 "Impl" => %{
                   "Ty" => %{
                     "kind" => "InherentImplBlock",
                     "params" => parent_params,
                     "skip_binder" => parent
                   }
                 }
               },
               %{"Ident" => [name, 0]}
             ]
           },
           "value" => %{
             "Value" => [
               _,
               [%{"Call" => [%{"kind" => %{"Fun" => init}, "generics" => args}, []]}, value_type]
             ]
           }
         } <- global,
         true <- name in ~w(MIN MAX BITS),
         true <-
           parameters?(params) and parameters?(parent_params) and Constants.empty_arguments?(args),
         %{"Scalar" => %{"Integer" => %{} = integer}} = scalar <-
           CallModels.expand(parent, refs),
         [{kind, width}] <- Map.to_list(integer),
         true <-
           (kind == "Unsigned" and width in ~w(U8 U16 U32 U64 U128)) or
             (kind == "Signed" and width in ~w(I8 I16 I32 I64 I128)),
         expected =
           if(name == "BITS",
             do: %{"Scalar" => %{"Integer" => %{"Unsigned" => "U32"}}},
             else: scalar
           ),
         true <-
           CallModels.expand(global["ty"], refs) == expected and
             CallModels.expand(value_type, refs) == expected,
         [initializer] <- Enum.filter(functions, &(&1 && &1["def_id"] == init)),
         true <-
           get_in(initializer, ["src", "GlobalInitializer", "id"]) == global["def_id"] and
             Constants.empty_arguments?(
               get_in(initializer, ["src", "GlobalInitializer", "generics"])
             ) and
             parameters?(initializer["generics"]) and
             initializer["item_meta"]["name"] == global["item_meta"]["name"] and
             initializer["item_meta"]["opacity"] == "Opaque" and
             initializer["body"] == "Opaque" and
             initializer["signature"]["is_unsafe"] == false and
             initializer["signature"]["is_variadic"] == false and
             initializer["signature"]["abi"] == "Rust" and
             initializer["signature"]["inputs"] == [] and
             CallModels.expand(initializer["signature"]["output"], refs) == expected do
      %{
        "lean_name" => "Aeneas.Std.core.num.#{width}.#{name}",
        "rust_name" => "core::num::{#{String.downcase(width)}}::#{name}",
        "can_fail" => false,
        "implementation_verified" => false,
        "label" =>
          "Aeneas Rust #{width}.#{name} primitive scalar constant model; standard core initializer not implementation verified"
      }
    else
      _ -> nil
    end
  end

  defp parameters?(%{
         "regions" => [],
         "types" => [],
         "const_generics" => [],
         "trait_clauses" => [],
         "outlives" => [],
         "trait_type_constraints" => []
       }),
       do: true

  defp parameters?(_), do: false
end
