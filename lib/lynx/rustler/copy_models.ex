defmodule Lynx.Rustler.CopyModels do
  @moduledoc false
  alias Lynx.Rust.{CallModels, ResourceModels}

  # These SDK wrappers are Copy: derived Clone copies their term/environment
  # handles, not resource ownership. Native handle validity remains an FFI model.
  def resolve(function, translated, refs) do
    with %{
           "body" => "Opaque",
           "src" => %{"TraitImpl" => source},
           "signature" => %{"abi" => "Rust", "is_unsafe" => false, "is_variadic" => false} = sig
         } <- function,
         %{
           "impl_ref" => %{"id" => impl_id},
           "trait_ref" => %{"id" => trait_id},
           "item_id" => 0,
           "reuses_default" => false
         } <- source,
         %{"item_meta" => %{"name" => trait_name}} <- find(translated["trait_decls"], trait_id),
         true <- trait_name == path(~w(core clone Clone)),
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}} = self <-
           CallModels.expand(sig["output"], refs),
         %{"kind" => "Opaque", "item_meta" => %{"name" => type_name}} <-
           find(translated["type_decls"], id),
         kind when kind in [:term, :atom] <- kind(type_name),
         regions = if(kind == :term, do: [region(0)], else: []),
         true <- args == %{ResourceModels.args([]) | "regions" => regions},
         true <-
           source["impl_ref"]["generics"] == %{ResourceModels.args([]) | "regions" => regions},
         true <-
           CallModels.expand(source["trait_ref"]["generics"], refs) == ResourceModels.args([self]),
         true <- copy?(self, translated, refs),
         count = if(kind == :term, do: 2, else: 1),
         true <- params?(function["generics"], count, kind),
         true <-
           CallModels.expand(sig["inputs"], refs) == [
             %{"Ref" => [region(count - 1), self, "Shared"]}
           ],
         prefix = if(kind == :term, do: ~w(rustler term), else: ~w(rustler types atom)),
         true <-
           function["item_meta"]["name"] ==
             path(prefix) ++ [%{"Impl" => %{"Trait" => impl_id}}, %{"Ident" => ["clone", 0]}],
         %{
           "src" => "Normal",
           "is_negative" => false,
           "is_unsafe" => false,
           "impl_trait" => implemented
         } <- find(translated["trait_impls"], impl_id),
         true <- implemented["id"] == trait_id,
         impl = find(translated["trait_impls"], impl_id),
         true <- impl_params?(impl["generics"], regions),
         true <- CallModels.expand(implemented["generics"], refs) == ResourceModels.args([self]),
         [%{"skip_binder" => %{"id" => method_id}} | _] <- impl["methods"],
         true <- method_id == function["def_id"] do
      rust_type =
        if kind == :term, do: "rustler::term::Term<'a>", else: "rustler::types::atom::Atom"

      lean =
        if(kind == :term, do: "Lynx.Rustler.copyTermHandle", else: "Lynx.Rustler.copyAtomHandle")

      %{
        rust_name: Enum.join(prefix, "::") <> "::{core::clone::Clone<#{rust_type}>}::clone",
        lean: lean,
        builtin: false,
        can_fail: true,
        native_cutoff_only: true,
        lift: true,
        label:
          "Rustler Copy-wrapper Clone model: identity of the same term/environment handle; no native resource retain or environment transfer; SDK bodies and FFI handle validity unverified"
      }
    else
      _ -> nil
    end
  end

  # A real Copy dictionary supplies the no-destructor certificate for Term's
  # lifetime-parametric type, whose generic needs_drop query may be unknown.
  defp copy?(self, translated, refs) do
    Enum.any?(translated["trait_impls"], fn impl ->
      with %{
             "src" => "Normal",
             "is_negative" => false,
             "is_unsafe" => false,
             "impl_trait" => %{"id" => id, "generics" => args}
           } <- impl,
           %{"item_meta" => %{"name" => name}} <- find(translated["trait_decls"], id) do
        name == path(~w(core marker Copy)) and impl["methods"] == [] and
          impl_params?(impl["generics"], self["Adt"]["generics"]["regions"]) and
          CallModels.expand(args, refs) == ResourceModels.args([self])
      else
        _ -> false
      end
    end)
  end

  defp impl_params?(params, regions) when is_map(params) do
    params["types"] == [] and params["const_generics"] == [] and
      params["trait_clauses"] == [] and params["trait_type_constraints"] == [] and
      params["outlives"] == [] and
      Enum.map(params["regions"], &region(&1["index"])) == regions
  end

  defp impl_params?(_, _), do: false

  defp kind(name) do
    cond do
      name == path(~w(rustler term Term)) -> :term
      name == path(~w(rustler types atom Atom)) -> :atom
      true -> nil
    end
  end

  defp params?(params, count, kind) do
    params["types"] == [] and params["const_generics"] == [] and
      params["trait_clauses"] == [] and params["trait_type_constraints"] == [] and
      Enum.map(params["regions"], & &1["index"]) == Enum.to_list(0..(count - 1)) and
      params["outlives"] ==
        if(kind == :term,
          do: [%{"regions" => [], "outlives" => [], "skip_binder" => [region(0), region(1)]}],
          else: []
        )
  end

  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})
  defp region(id), do: %{"Var" => %{"Free" => id}}
  defp find(values, id), do: Enum.find(values, &(&1 && &1["def_id"] == id))
end
