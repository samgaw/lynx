defmodule Lynx.Rust.TryModels do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LLBC, ResourceModels}

  # Reuse Aeneas's Result/Try primitives. The FromResidual callback is admitted
  # only with the concrete standard identity From dictionary at every call site.
  # No user conversion body is erased or replaced by an assumed identity.
  # Option uses downstream total enum models over the exact Never residual.
  # Invalid enum representations and custom Try implementations are not admitted.
  def resolve(f, t, refs) do
    with %{"body" => "Opaque", "src" => %{"TraitImpl" => src}, "signature" => sig} <- f,
         true <-
           sig["abi"] == "Rust" and sig["is_unsafe"] == false and sig["is_variadic"] == false,
         false <- src["reuses_default"],
         impl when not is_nil(impl) <- find(t["trait_impls"], src["impl_ref"]["id"]),
         true <-
           impl["src"] == "Normal" and impl["is_unsafe"] == false and impl["is_negative"] == false,
         trait when not is_nil(trait) <- find(t["trait_decls"], impl["impl_trait"]["id"]),
         true <- trait["src"] == "Normal" and trait["is_unsafe"] == false,
         true <- src["trait_ref"]["id"] == trait["def_id"],
         true <-
           Enum.count(impl["methods"], fn m ->
             m["kind"] == %{"TraitMethod" => [trait["def_id"], src["item_id"]]} and
               m["skip_binder"]["id"] == f["def_id"]
           end) == 1 do
      input = CallModels.expand(sig["inputs"], refs)
      output = CallModels.expand(sig["output"], refs)
      implemented = expand_args(impl["impl_trait"]["generics"], refs)
      selected = select(f, impl, trait, input, output, implemented, t, refs)

      if selected do
        {rust, lean, extra} = selected

        Map.merge(
          %{
            rust_name: rust,
            lean: if(String.starts_with?(lean, "Lynx."), do: lean, else: "Aeneas.Std." <> lean),
            builtin: true,
            can_fail: lean != "core.convert.FromSame.from",
            lift: false,
            native_transfer: true,
            native_cutoff_only: true,
            label:
              "Aeneas standard Result/Try and identity From models; exact enum, signature and trait implementation admission; custom residual conversions rejected; Rust core implementation not verified"
          },
          extra
        )
      end
    else
      _ -> nil
    end
  end

  defp select(f, impl, trait, input, output, implemented, t, refs) do
    cond do
      named?(f, impl, ~w(core convert), "from") and
        f["src"]["TraitImpl"]["item_id"] == 0 and length(impl["methods"]) == 1 and
        trait["item_meta"]["name"] == name(~w(core convert From)) and
        parameters?(trait["generics"], 2, 0) and
        parameters?(f["generics"], 1, 0) and parameters?(impl["generics"], 1, 0) and
        input == [var(0)] and output == var(0) and implemented == args([var(0), var(0)]) ->
        {"core::convert::{core::convert::From<@T, @T>}::from", "core.convert.FromSame.from",
         %{try_identity: trait["def_id"]}}

      named?(f, impl, ~w(core result), "branch") and
        f["src"]["TraitImpl"]["item_id"] == 1 and length(impl["methods"]) == 2 and
        trait["item_meta"]["name"] == name(~w(core ops try_trait Try)) and
        parameters?(trait["generics"], 1, 0) and
        parameters?(f["generics"], 2, 0) and parameters?(impl["generics"], 2, 0) ->
        with [r] <- input,
             true <- result?(r, [var(0), var(1)], t, refs),
             true <- implemented == args([r]),
             %{"Adt" => %{"id" => flow, "builtin" => nil, "generics" => g}} <- output,
             [residual, value] <- g["types"],
             true <- g == args([residual, var(0)]) and value == var(0),
             true <- result?(residual, ["Never", var(1)], t, refs),
             true <- control_flow?(flow, t, refs) do
          {"core::result::{core::ops::try_trait::Try<core::result::Result<@T, @E>>}::branch",
           "core.result.Result.Insts.CoreOpsTry.branch", %{}}
        else
          _ -> nil
        end

      named?(f, impl, ~w(core result), "from_residual") and
        f["src"]["TraitImpl"]["item_id"] == 0 and length(impl["methods"]) == 1 and
        trait["item_meta"]["name"] == name(~w(core ops try_trait FromResidual)) and
        parameters?(trait["generics"], 2, 0) and
        parameters?(f["generics"], 3, 1) and parameters?(impl["generics"], 3, 1) ->
        with [r] <- input,
             true <- result?(r, ["Never", var(1)], t, refs),
             true <- result?(output, [var(0), var(2)], t, refs),
             true <- implemented == args([output, r]),
             from when not is_nil(from) <- named(t["trait_decls"], ~w(core convert From)),
             [clause] <- f["generics"]["trait_clauses"],
             true <- from_clause?(clause, from["def_id"], refs),
             [clause] <- impl["generics"]["trait_clauses"],
             true <- from_clause?(clause, from["def_id"], refs) do
          {"core::result::{core::ops::try_trait::FromResidual<core::result::Result<@T, @F>, core::result::Result<!, @E>>}::from_residual",
           "core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual",
           %{try_residual: from["def_id"]}}
        else
          _ -> nil
        end

      named?(f, impl, ~w(core option), "branch") and
        f["src"]["TraitImpl"]["item_id"] == 1 and length(impl["methods"]) == 2 and
        trait["item_meta"]["name"] == name(~w(core ops try_trait Try)) and
        parameters?(trait["generics"], 1, 0) and
        parameters?(f["generics"], 1, 0) and parameters?(impl["generics"], 1, 0) ->
        with [option] <- input,
             true <- option?(option, var(0), t, refs),
             true <- implemented == args([option]),
             %{"Adt" => %{"id" => flow, "builtin" => nil, "generics" => g}} <- output,
             [residual, value] <- g["types"],
             true <- g == args([residual, var(0)]) and value == var(0),
             true <- option?(residual, "Never", t, refs),
             true <- control_flow?(flow, t, refs) do
          {"core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch",
           "Lynx.Rust.Try.optionBranch", option_model()}
        else
          _ -> nil
        end

      named?(f, impl, ~w(core option), "from_residual") and
        f["src"]["TraitImpl"]["item_id"] == 0 and length(impl["methods"]) == 1 and
        trait["item_meta"]["name"] == name(~w(core ops try_trait FromResidual)) and
        parameters?(trait["generics"], 2, 0) and
        parameters?(f["generics"], 1, 0) and parameters?(impl["generics"], 1, 0) ->
        with [residual] <- input,
             true <- option?(residual, "Never", t, refs),
             true <- option?(output, var(0), t, refs),
             true <- implemented == args([output, residual]) do
          {"core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<!>>}::from_residual",
           "Lynx.Rust.Try.optionFromResidual", option_model()}
        else
          _ -> nil
        end

      true ->
        nil
    end
  end

  defp option_model do
    %{
      builtin: false,
      can_fail: false,
      lift: true,
      label:
        "Standard Option Try/FromResidual enum model: Some continues and None returns early; exact Option/ControlFlow and Never residual identities required; Rust core implementation not verified"
    }
  end

  defp option?(%{"Adt" => %{"id" => id, "builtin" => nil, "generics" => g}}, type, t, refs),
    do: g == args([type]) and LLBC.option_type?(id, %{translated: t, references: refs})

  defp option?(_, _, _, _), do: false

  def audit(functions, models, t, refs) do
    traits = ResourceModels.trait_references(t)

    Enum.reduce_while(functions, {:ok, %{}}, fn f, {:ok, deps} ->
      try do
        {:cont, {:ok, merge(deps, calls!(f["body"], models, t, refs, traits))}}
      rescue
        e in ArgumentError -> {:halt, {:error, f, Exception.message(e)}}
      end
    end)
  end

  defp calls!(
         %{"Regular" => %{"kind" => %{"Fun" => id}, "generics" => g}},
         models,
         t,
         refs,
         traits
       ) do
    case models[id] do
      %{try_residual: from} ->
        with %{
               "regions" => [],
               "types" => [_, e, f],
               "const_generics" => [],
               "trait_refs" => [dict]
             } <- g,
             true <- CallModels.expand(e, refs) == CallModels.expand(f, refs),
             %{
               "kind" => %{"TraitImpl" => %{"id" => impl, "generics" => ig}},
               "trait_decl_ref" => decl
             } <- ResourceModels.dictionary(dict, traits),
             true <- expand_args(ig, refs) == args([CallModels.expand(e, refs)]),
             true <-
               decl["id"] == from and
                 expand_args(decl["generics"], refs) == args(CallModels.expand([e, e], refs)),
             impl when not is_nil(impl) <- find(t["trait_impls"], impl),
             [%{"skip_binder" => %{"id" => method}}] <- impl["methods"],
             function when not is_nil(function) <- find(t["fun_decls"], method),
             %{try_identity: ^from} <- resolve(function, t, refs) do
          %{id => [method]}
        else
          _ ->
            raise ArgumentError,
                  "Result ? requires the concrete standard identity From conversion; custom or unresolved error conversions are unsupported"
        end

      _ ->
        %{}
    end
  end

  defp calls!(m, models, t, refs, traits) when is_map(m),
    do: calls!(Map.values(m), models, t, refs, traits)

  defp calls!(l, models, t, refs, traits) when is_list(l),
    do: Enum.reduce(l, %{}, &merge(&2, calls!(&1, models, t, refs, traits)))

  defp calls!(_, _, _, _, _), do: %{}
  defp merge(a, b), do: Map.merge(a, b, fn _, x, y -> Enum.uniq(x ++ y) end)

  defp control_flow?(id, t, refs) do
    case find(t["type_decls"], id) do
      %{"item_meta" => %{"name" => n}, "kind" => %{"Enum" => [a, b]}, "generics" => p} ->
        n == name(~w(core ops control_flow ControlFlow)) and parameters?(p, 2, 0) and
          Enum.all?([{a, 0, "Continue", 1}, {b, 1, "Break", 0}], fn {v, index, label, param} ->
            v["id"] == index and v["name"] == label and
              v["discriminant"] == %{"Signed" => ["Isize", Integer.to_string(index)]} and
              match?([_], v["fields"]) and
              CallModels.expand(hd(v["fields"])["ty"], refs) == var(param)
          end)

      _ ->
        false
    end
  end

  defp result?(%{"Adt" => %{"id" => id, "builtin" => nil, "generics" => g}}, types, t, refs),
    do: g == args(types) and LLBC.result_type?(id, %{translated: t, references: refs})

  defp result?(_, _, _, _), do: false

  defp from_clause?(
         %{
           "clause_id" => 0,
           "trait_" => %{"regions" => [], "outlives" => [], "skip_binder" => decl}
         },
         id,
         refs
       ),
       do: decl["id"] == id and expand_args(decl["generics"], refs) == args([var(2), var(1)])

  defp from_clause?(_, _, _), do: false

  defp named?(f, impl, prefix, method),
    do:
      impl["item_meta"]["name"] == name(prefix) ++ [%{"Impl" => %{"Trait" => impl["def_id"]}}] and
        f["item_meta"]["name"] == impl["item_meta"]["name"] ++ name([method])

  defp parameters?(p, n, c),
    do:
      p["regions"] == [] and p["const_generics"] == [] and p["outlives"] == [] and
        p["trait_type_constraints"] == [] and
        Enum.map(p["types"], & &1["index"]) == Enum.to_list(0..(n - 1)//1) and
        length(p["trait_clauses"]) == c

  defp named(items, path) do
    case Enum.filter(items, &(&1 && &1["item_meta"]["name"] == name(path))) do
      [x] -> x
      _ -> nil
    end
  end

  defp find(items, id) do
    case Enum.filter(items, &(&1 && &1["def_id"] == id)) do
      [item] -> item
      _ -> nil
    end
  end

  defp name(path), do: Enum.map(path, &%{"Ident" => [&1, 0]})
  defp var(i), do: %{"TypeVar" => %{"Free" => i}}

  defp args(types),
    do: %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}

  defp expand_args(g, refs), do: Map.update!(g, "types", &CallModels.expand(&1, refs))
end
