defmodule Lynx.Rust.StringSplits do
  @moduledoc false
  alias Lynx.Rust.{CallModels, OptionModels, ResourceModels, StringModels}

  def checked_body?(function, translated, refs) do
    match?(%{"Structured" => _}, function["body"]) and
      signature?(function, translated, refs, "split_at_checked", false)
  end

  def resolve(function, translated, refs) do
    if function["body"] == "Opaque" and
         signature?(function, translated, refs, "split_at_unchecked", true) do
      %{
        rust_name: "core::str::{str}::split_at_unchecked",
        lean: "StringSlices.splitUnchecked",
        builtin: false,
        can_fail: true,
        lift: true,
        string_slice_op: "splitUnchecked",
        str_split_unchecked: true,
        model_digest: Lynx.Rust.StringSliceModels.fingerprint(),
        label:
          "Shared str unchecked borrowing primitive, restricted to the extracted standard split_at_checked body; invalid byte boundaries exhaust verification; native pointer arithmetic, layout and borrow lifetime remain unverified"
      }
    end
  end

  defp signature?(f, t, refs, method, unsafe) do
    with %{
           "src" => "Normal",
           "signature" =>
             %{"abi" => "Rust", "is_variadic" => false, "is_unsafe" => ^unsafe} = sig,
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
               %{"Ident" => [^method, 0]}
             ]
           },
           "generics" => p
         } <- f,
         true <- parent_params == params(),
         true <- match?([%{"index" => 0}], p["regions"]),
         true <- Map.put(p, "regions", []) == params(),
         str = CallModels.expand(parent, refs),
         borrowed = %{"Ref" => [%{"Var" => %{"Free" => 0}}, str, "Shared"]},
         true <- StringModels.borrowed_type?(borrowed, t, refs),
         true <- CallModels.expand(sig["inputs"], refs) == [borrowed, usize()],
         output = CallModels.expand(sig["output"], refs) do
      if unsafe do
        pair?(output, borrowed, t)
      else
        with %{"Adt" => %{"builtin" => nil, "id" => id, "generics" => actual}} <- output,
             [pair] <- actual["types"],
             true <- actual == ResourceModels.args([pair]),
             type when is_map(type) <- Enum.find(t["type_decls"], &(&1 && &1["def_id"] == id)) do
          OptionModels.option_type?(type, refs) and pair?(pair, borrowed, t)
        else
          _ -> false
        end
      end
    else
      _ -> false
    end
  end

  defp pair?(%{"Adt" => %{"builtin" => "Tuple", "id" => id, "generics" => args}}, borrowed, t) do
    args == ResourceModels.args([borrowed, borrowed]) and
      Enum.any?(t["type_decls"], fn type ->
        type && type["def_id"] == id && type["src"] == %{"Builtin" => "Tuple"} &&
          type["kind"] == "Opaque" && type["generics"] == params() &&
          type["item_meta"]["name"] == [%{"Builtin" => [%{"Tuple" => 0}, 0]}]
      end)
  end

  defp pair?(_, _, _), do: false
  defp usize, do: %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}

  defp params,
    do:
      Map.new(
        ~w(regions types const_generics trait_clauses outlives trait_type_constraints),
        &{&1, []}
      )
end
