defmodule Lynx.Rust.VectorSplits do
  @moduledoc false
  alias Lynx.Rust.{CallModels, FormatModels, ResourceModels, VectorExtensions}

  def resolve(function, translated, refs) do
    f = CallModels.expand(function, refs)

    with %{
           "body" => "Opaque",
           "src" => "Normal",
           "signature" => %{"abi" => "Rust", "is_unsafe" => false, "is_variadic" => false} = sig,
           "generics" => params,
           "item_meta" => %{"name" => [a, b, %{"Impl" => %{"Ty" => parent}}, c]}
         } <- f,
         true <- [a, b, c] == path(~w(alloc vec split_off)),
         true <- parent["kind"] == "InherentImplBlock" and parameters?(parent["params"], 0, 2),
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}} = vector <-
           free(parent["skip_binder"]),
         true <- args == args([var(0)]),
         %{"kind" => "Opaque", "generics" => type_params, "item_meta" => %{"name" => name}} <-
           find(translated["type_decls"], id),
         true <- name == path(~w(alloc vec Vec)) and parameters?(type_params, 0, 1),
         [clause] <- params["trait_clauses"],
         true <- parameters?(%{params | "trait_clauses" => [], "outlives" => []}, 1, 2),
         true <- params["outlives"] == Enum.map(0..1, &outlives/1),
         %{
           "clause_id" => 0,
           "trait_" => %{
             "regions" => [],
             "outlives" => [],
             "skip_binder" => %{"id" => trait, "generics" => bound}
           }
         } <- clause,
         true <-
           bound == args([var(1)]) and
             VectorExtensions.clone_trait?(find(translated["trait_decls"], trait), refs),
         true <- sig["inputs"] == [ref(vector, "Mut"), usize()] and sig["output"] == vector do
      %{
        rust_name: "alloc::vec::{alloc::vec::Vec<@T>}::split_off",
        lean: "Aeneas.Std.alloc.vec.Vec.split_off",
        builtin: false,
        can_fail: true,
        lift: true,
        keep_params: [true, false],
        keep_trait_clauses: [false],
        vec_owned_method: "split_off",
        native_cutoff_only: false,
        label:
          "Logical Vec::split_off model for concrete u8 and the exact standard Global/Clone allocator dictionary; preserves returned suffix and retained prefix, panics when index exceeds length before allocation; valid splits above 262144 input bytes exhaust verification; capacity, Rust std, allocation failure and native allocation/copy correctness unverified; guarded mutable-borrow panic outputs remain unsupported"
      }
    else
      _ -> nil
    end
  end

  # Erase only the standard Global allocator's known, callback-free Clone.
  # A name/signature match at the split call alone is not a dictionary witness.
  def valid_call?(args, translated, refs) do
    with true <- args["const_generics"] == [],
         [dict] <- args["trait_refs"],
         [element, allocator] <- CallModels.expand(args["types"], refs),
         true <- element == byte(),
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => empty}} <- allocator,
         true <- empty == args([]),
         %{
           "src" => "Normal",
           "kind" => "Opaque",
           "generics" => tp,
           "item_meta" => %{"name" => name}
         } <- find(translated["type_decls"], id),
         true <- name == path(~w(alloc alloc Global)) and parameters?(tp, 0, 0),
         %{
           "kind" => %{"TraitImpl" => %{"id" => impl_id, "generics" => empty}},
           "trait_decl_ref" => %{"id" => trait, "generics" => actual}
         } <- ResourceModels.dictionary(dict, ResourceModels.trait_references(translated)),
         true <- empty == args([]) and CallModels.expand(actual, refs) == args([allocator]),
         true <- VectorExtensions.clone_trait?(find(translated["trait_decls"], trait), refs),
         impl when not is_nil(impl) <- find(translated["trait_impls"], impl_id),
         impl = CallModels.expand(impl, refs),
         true <-
           impl["src"] == "Normal" and impl["is_negative"] == false and impl["is_unsafe"] == false,
         true <-
           impl["item_meta"]["name"] ==
             path(~w(alloc alloc)) ++ [%{"Impl" => %{"Trait" => impl_id}}],
         true <- parameters?(impl["generics"], 0, 0),
         true <- impl["consts"] == [] and impl["types"] == [] and impl["implied_trait_refs"] == [],
         true <- impl["impl_trait"] == %{"id" => trait, "generics" => args([allocator])},
         [method, nil] <- impl["methods"],
         f when not is_nil(f) <- find(translated["fun_decls"], method["skip_binder"]["id"]),
         f = CallModels.expand(f, refs),
         true <- f["item_meta"]["name"] == impl["item_meta"]["name"] ++ path(~w(clone)),
         true <- f["body"] == "Opaque" and parameters?(f["generics"], 1, 0),
         true <-
           f["signature"] == %{
             "abi" => "Rust",
             "is_unsafe" => false,
             "is_variadic" => false,
             "inputs" => [ref(allocator, "Shared")],
             "output" => allocator
           },
         true <-
           FormatModels.method_identity?(f, %{impl | "methods" => [method]}, trait, %{
             translated: translated,
             refs: refs,
             traits: %{}
           }) do
      true
    else
      _ -> false
    end
  end

  def lean do
    """
      @[expose] def split_off {α : Type} (values : alloc.vec.Vec α) (position : Usize) :
          RustM (alloc.vec.Vec α × alloc.vec.Vec α) :=
        if position.val ≤ values.val.length then
          if values.val.length ≤ 262144 then
            .ok (alloc.vec.Vec.from (values.val.drop position.val) (by
                have h := values.property; simp only [List.length_drop]; omega),
              alloc.vec.Vec.from (values.val.take position.val) (by
                have h := values.property; simp only [List.length_take]; omega))
          else .fail .undef
        else .fail .panic
      theorem split_off_eq {α : Type} (values : alloc.vec.Vec α) (position : Usize)
          (inside : position.val ≤ values.val.length) (bound : values.val.length ≤ 262144) :
          split_off values position = RustM.ok
            (alloc.vec.Vec.from (values.val.drop position.val) (by have h := values.property; simp only [List.length_drop]; omega),
              alloc.vec.Vec.from (values.val.take position.val) (by have h := values.property; simp only [List.length_take]; omega)) := by
        simp [split_off, inside, bound]
      theorem split_off_panic {α : Type} (values : alloc.vec.Vec α) (position : Usize)
          (outside : values.val.length < position.val) : split_off values position = RustM.fail .panic := by
        simp [split_off, Nat.not_le.mpr outside]
      theorem split_off_cutoff {α : Type} (values : alloc.vec.Vec α) (position : Usize)
          (inside : position.val ≤ values.val.length) (outside : ¬values.val.length ≤ 262144) :
          split_off values position = RustM.fail .undef := by simp [split_off, inside, outside]
    """
  end

  defp parameters?(p, regions, types),
    do:
      is_map(p) and Enum.map(p["regions"] || [], & &1["index"]) == indices(regions) and
        Enum.map(p["types"] || [], & &1["index"]) == indices(types) and
        Enum.all?(
          ~w(const_generics trait_clauses trait_type_constraints outlives),
          &(p[&1] == [])
        )

  defp indices(0), do: []
  defp indices(n), do: Enum.to_list(0..(n - 1))

  defp outlives(i),
    do: %{
      "regions" => [],
      "outlives" => [],
      "skip_binder" => [%{"Lub" => var(i)}, %{"Var" => %{"Free" => 0}}]
    }

  defp args(types), do: ResourceModels.args(types)
  defp var(i), do: %{"TypeVar" => %{"Free" => i}}
  defp byte, do: %{"Scalar" => %{"Integer" => %{"Unsigned" => "U8"}}}
  defp usize, do: %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}
  defp ref(type, kind), do: %{"Ref" => [%{"Var" => %{"Free" => 0}}, type, kind]}
  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})
  defp find(items, id), do: Enum.find(items || [], &(&1 && &1["def_id"] == id))
  defp free(%{"Bound" => [0, index]}), do: %{"Free" => index}
  defp free(map) when is_map(map), do: Map.new(map, fn {k, v} -> {k, free(v)} end)
  defp free(list) when is_list(list), do: Enum.map(list, &free/1)
  defp free(value), do: value
end
