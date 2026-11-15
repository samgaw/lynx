defmodule Lynx.Rust.VectorExtensions do
  @moduledoc false
  alias Lynx.Rust.{CallModels, FormatModels, ResourceModels}

  def resolve(function, translated, refs),
    do: extend(function, translated, refs) || clone(function, translated, refs)

  defp extend(function, translated, refs) do
    function = CallModels.expand(function, refs)

    with %{
           "body" => "Opaque",
           "src" => "Normal",
           "generics" => params,
           "signature" => %{"abi" => "Rust", "is_unsafe" => false, "is_variadic" => false} = sig,
           "item_meta" => %{
             "name" => [
               %{"Ident" => ["alloc", 0]},
               %{"Ident" => ["vec", 0]},
               %{
                 "Impl" => %{
                   "Ty" => %{
                     "kind" => "InherentImplBlock",
                     "params" => parent,
                     "skip_binder" => self
                   }
                 }
               },
               %{"Ident" => ["extend_from_slice", 0]}
             ]
           }
         } <- function,
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}} <- free(self),
         true <- args == args([var(0)]),
         type when not is_nil(type) <- find(translated["type_decls"], id),
         true <- type["kind"] == "Opaque" and type["item_meta"]["name"] == path(~w(alloc vec Vec)),
         true <- params?(type["generics"], 0, 1),
         true <- extend_params?(params, parent, translated, refs),
         true <-
           sig["inputs"] == [
             ref(
               %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args([var(0)])}},
               0,
               "Mut"
             ),
             ref(%{"Slice" => [var(0), nil]}, 1, "Shared")
           ],
         true <- unit?(sig["output"]) do
      %{
        rust_name: "alloc::vec::Vec::extend_from_slice",
        lean: "Aeneas.Std.alloc.vec.Vec.extend_from_slice",
        builtin: true,
        can_fail: true,
        lift: true,
        keep_params: [true, false],
        vec_owned_method: "extend_from_slice",
        native_cutoff_only: true,
        label:
          "Bounded upstream Vec::extend_from_slice model: only concrete u8 elements, exact standard Clone and Global allocator admitted; preserves prefix and byte order; total length above 262144 exhausts verification, not Rust rejection; Rust std, capacity, allocator effects and allocation failure unverified"
      }
    else
      _ -> nil
    end
  end

  defp extend_params?(params, parent, translated, refs) do
    with [clause] <- params["trait_clauses"],
         [parent_clause] <- parent["trait_clauses"],
         true <- params?(%{params | "trait_clauses" => [], "outlives" => []}, 2, 2),
         true <- params?(%{parent | "trait_clauses" => []}, 0, 2),
         %{
           "clause_id" => 0,
           "trait_" => %{
             "regions" => [],
             "outlives" => [],
             "skip_binder" => %{"id" => id, "generics" => actual}
           }
         } <- clause,
         %{
           "clause_id" => 0,
           "trait_" => %{
             "regions" => [],
             "outlives" => [],
             "skip_binder" => %{"id" => ^id, "generics" => inherited}
           }
         } <- parent_clause,
         true <- clone_trait?(find(translated["trait_decls"], id), refs),
         true <-
           actual == args([var(0)]) and inherited == args([%{"TypeVar" => %{"Bound" => [1, 0]}}]),
         true <-
           params["outlives"] ==
             Enum.map([{0, 0}, {1, 0}, {0, 1}], fn {t, r} ->
               %{
                 "regions" => [],
                 "outlives" => [],
                 "skip_binder" => [%{"Lub" => var(t)}, %{"Var" => %{"Free" => r}}]
               }
             end) do
      true
    else
      _ -> false
    end
  end

  defp clone(function, translated, refs) do
    function = CallModels.expand(function, refs)

    with %{
           "body" => "Opaque",
           "src" => %{"TraitImpl" => source},
           "generics" => params,
           "signature" => %{"abi" => "Rust", "is_unsafe" => false, "is_variadic" => false} = sig
         } <- function,
         true <- params?(params, 1, 0),
         true <- sig["inputs"] == [ref(byte(), 0, "Shared")] and sig["output"] == byte(),
         %{"id" => impl_id} <- source["impl_ref"],
         %{"id" => trait} <- source["trait_ref"],
         true <- clone_trait?(find(translated["trait_decls"], trait), refs),
         impl when not is_nil(impl) <- find(translated["trait_impls"], impl_id),
         impl = CallModels.expand(impl, refs),
         name = path(~w(core clone impls)) ++ [%{"Impl" => %{"Trait" => impl_id}}],
         true <- function["item_meta"]["name"] == name ++ path(~w(clone)),
         true <- impl["item_meta"]["name"] == name and impl["src"] == "Normal",
         true <- impl["is_negative"] == false and impl["is_unsafe"] == false,
         true <- params?(impl["generics"], 0, 0),
         true <- impl["consts"] == [] and impl["types"] == [] and impl["implied_trait_refs"] == [],
         true <- impl["impl_trait"] == %{"id" => trait, "generics" => args([byte()])},
         [method, nil] <- impl["methods"],
         true <-
           FormatModels.method_identity?(function, %{impl | "methods" => [method]}, trait, %{
             translated: translated,
             refs: refs,
             traits: %{}
           }) do
      %{
        rust_name: "core::clone::impls::Clone<u8>::clone",
        lean: "Aeneas.Std.core.clone.impls.CloneU8.clone",
        builtin: true,
        can_fail: false,
        lift: false,
        label:
          "Upstream primitive u8 Clone identity model; actual standard trait, impl, method and signature checked; Rust core implementation unverified"
      }
    else
      _ -> nil
    end
  end

  # The allocator is audited separately by CollectionModels. Retain the actual
  # Clone dictionary and reject opaque/custom callbacks before pruning unwind.
  def valid_call?(arguments, translated, refs) do
    arguments = Map.update!(arguments, "types", &CallModels.expand(&1, refs))
    traits = ResourceModels.trait_references(translated)

    with %{
           "types" => [element, _],
           "regions" => [_, _],
           "const_generics" => [],
           "trait_refs" => [dict]
         } <- arguments,
         true <- element == byte(),
         %{
           "kind" => %{"TraitImpl" => %{"id" => impl_id, "generics" => empty}},
           "trait_decl_ref" => decl
         } <- ResourceModels.dictionary(dict, traits),
         true <- empty == args([]),
         impl when not is_nil(impl) <- find(translated["trait_impls"], impl_id),
         [method, nil] <- impl["methods"],
         function when not is_nil(function) <-
           find(translated["fun_decls"], method["skip_binder"]["id"]),
         model when not is_nil(model) <- clone(function, translated, refs),
         true <- model.can_fail == false,
         true <-
           decl["id"] == impl["impl_trait"]["id"] and
             CallModels.expand(decl["generics"], refs) == args([byte()]) do
      true
    else
      _ -> false
    end
  end

  def lean do
    """
      @[expose] def extend_from_slice {α : Type} (clone : core.clone.Clone α)
          (values : alloc.vec.Vec α) (input : Slice α) : RustM (alloc.vec.Vec α) :=
        if values.val.length + input.val.length ≤ 262144 then
          alloc.vec.Vec.extend_from_slice clone values input else RustM.fail .undef
      theorem extend_within {α : Type} (clone : core.clone.Clone α)
          (values : alloc.vec.Vec α) (input : Slice α)
          (bound : values.val.length + input.val.length ≤ 262144) :
          extend_from_slice clone values input = alloc.vec.Vec.extend_from_slice clone values input := by
        simp [extend_from_slice, bound]
      theorem extend_cutoff {α : Type} (clone : core.clone.Clone α)
          (values : alloc.vec.Vec α) (input : Slice α)
          (bound : ¬ values.val.length + input.val.length ≤ 262144) :
          extend_from_slice clone values input = RustM.fail .undef := by
        simp [extend_from_slice, bound]
      private theorem clone_bytes (input : List U8) :
          List.clone core.clone.CloneU8.clone input = RustM.ok ⟨input, rfl⟩ := by
        have spec := List.clone_spec (clone := core.clone.CloneU8.clone) (l := input) (by intros; rfl)
        cases result : List.clone core.clone.CloneU8.clone input with
        | ret output =>
          simp only [result, WP.spec_ok] at spec
          have same : output = ⟨input, rfl⟩ := Subtype.ext spec.1
          simp only [same]
        | vis event next => simp only [result, WP.spec_vis] at spec
        | div => simp only [result, WP.spec_div] at spec

      @[cbv_eval] theorem extend_bytes_eq (values : alloc.vec.Vec U8) (input : Slice U8) :
          extend_from_slice core.clone.CloneU8 values input =
            if bound : values.val.length + input.val.length ≤ 262144 then
              RustM.ok (alloc.vec.Vec.from (values.val ++ input.val) (by scalar_tac))
            else RustM.fail .undef := by
        split
        · rename_i bound
          have size : values.val.length + input.val.length ≤ Usize.max := by scalar_tac
          have clone := clone_bytes input.val
          change List.clone (liftFun1 core.clone.impls.CloneU8.clone) input.val = _ at clone
          simp only [extend_from_slice, ite_eq_left bound, alloc.vec.Vec.extend_from_slice,
            dite_eq_left size]
          rw [clone]
          simp
        · rename_i outside
          exact extend_cutoff core.clone.CloneU8 values input outside
    """
  end

  defp clone_trait?(nil, _), do: false

  defp clone_trait?(trait, refs) do
    trait = CallModels.expand(trait, refs)
    id = trait["def_id"]

    with true <- trait["item_meta"]["name"] == path(~w(core clone Clone)),
         true <- trait["item_meta"]["lang_item"] == "Clone",
         true <- trait["src"] == "Normal" and trait["is_unsafe"] == false,
         true <- params?(trait["generics"], 0, 1),
         true <- trait["consts"] == [] and trait["types"] == [] and trait["implied_clauses"] == [],
         [
           %{"kind" => %{"TraitMethod" => [^id, 0]}, "params" => params, "skip_binder" => method},
           nil
         ] <- trait["methods"],
         true <- params?(params, 1, 0),
         true <- method["name"] == "clone" and method["default"] == nil,
         true <- method["item_meta"]["name"] == path(~w(core clone Clone clone)),
         true <- method["item_meta"]["lang_item"] == "CloneFn",
         true <-
           method["signature"] == %{
             "abi" => "Rust",
             "is_unsafe" => false,
             "is_variadic" => false,
             "inputs" => [%{"Ref" => [%{"Var" => %{"Bound" => [0, 0]}}, var(0), "Shared"]}],
             "output" => var(0)
           } do
      true
    else
      _ -> false
    end
  end

  defp params?(params, regions, types),
    do:
      is_map(params) and
        Enum.map(params["regions"] || [], & &1["index"]) == indices(regions) and
        Enum.map(params["types"] || [], & &1["index"]) == indices(types) and
        Enum.all?(
          ~w(const_generics trait_clauses trait_type_constraints outlives),
          &(params[&1] == [])
        )

  defp indices(0), do: []
  defp indices(n), do: Enum.to_list(0..(n - 1))
  defp args(types), do: ResourceModels.args(types)
  defp byte, do: %{"Scalar" => %{"Integer" => %{"Unsigned" => "U8"}}}
  defp var(i), do: %{"TypeVar" => %{"Free" => i}}
  defp ref(type, region, kind), do: %{"Ref" => [%{"Var" => %{"Free" => region}}, type, kind]}
  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})
  defp find(items, id), do: Enum.find(items || [], &(&1 && &1["def_id"] == id))
  defp unit?(%{"Adt" => %{"builtin" => "Tuple", "generics" => args}}), do: args == args([])
  defp unit?(_), do: false
  defp free(%{"Bound" => [0, index]}), do: %{"Free" => index}
  defp free(map) when is_map(map), do: Map.new(map, fn {k, v} -> {k, free(v)} end)
  defp free(list) when is_list(list), do: Enum.map(list, &free/1)
  defp free(value), do: value
end
