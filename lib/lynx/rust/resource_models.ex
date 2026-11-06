defmodule Lynx.Rust.ResourceModels do
  @moduledoc false
  alias Lynx.Rust.{CallModels, FormatModels}
  @arc ~w(rustler resource arc ResourceArc)
  @resource ~w(rustler resource traits Resource)

  # Signatures alone cannot approve a resource: ResourceAudit checks concrete
  # dictionaries and payloads, ResourceDrops checks destruction, and standalone
  # properties state loader registration in their environment preconditions.

  def type?(%{"kind" => "Opaque", "item_meta" => %{"name" => name}, "generics" => p}),
    do: name == path(@arc) and params?(p, 0, [])

  def type?(_), do: false

  def resolve(f, t, refs) do
    with %{
           "body" => "Opaque",
           "signature" => %{"abi" => "Rust", "is_unsafe" => false, "is_variadic" => false} = sig
         } <- f,
         [arc] <- Enum.filter(t["type_decls"], &type?/1),
         [resource] <-
           Enum.filter(t["trait_decls"], &(&1 && &1["item_meta"]["name"] == path(@resource))),
         params = CallModels.expand(f["generics"], refs),
         [clause] <- params["trait_clauses"],
         true <- resource_clause?(clause, resource["def_id"], refs),
         method when method in ~w(new clone deref) <- method(f),
         n = if(method == "new", do: 0, else: 1),
         bounds = if(n == 0, do: [], else: [bound()]),
         true <- params?(params, n, [clause], bounds),
         sig = CallModels.expand(sig, refs),
         self = adt(arc["def_id"], variable()),
         true <- sig["inputs"] == if(method == "new", do: [variable()], else: [reference(self)]),
         true <- sig["output"] == if(method == "deref", do: reference(variable()), else: self),
         true <- identity?(f, method, self, resource["def_id"], t, refs) do
      rust =
        if method == "new",
          do: "rustler::resource::arc::{rustler::resource::arc::ResourceArc<@T>}::new",
          else:
            "rustler::resource::arc::{core::#{if method == "clone", do: "clone::Clone", else: "ops::deref::Deref"}<rustler::resource::arc::ResourceArc<@T>#{if method == "deref", do: ", @T", else: ""}>}::#{method}"

      %{
        rust_name: rust,
        lean:
          "Lynx.NativeResourceArc.#{if method == "new" and get_in(t, ["options", "owned_drops"]) == true, do: "newOwned", else: method}",
        builtin: false,
        can_fail: true,
        lift: true,
        keep_params: [true],
        keep_trait_clauses: [false],
        native_resource_type: arc["def_id"],
        resource_trait: resource["def_id"],
        resource_operation: method,
        native_transfer: method == "new" and get_in(t, ["options", "owned_drops"]) == true,
        native_cutoff_only: method != "new",
        label:
          if(get_in(t, ["options", "owned_drops"]) == true,
            do:
              "Rustler 0.39 ResourceArc with extracted payload cleanup: shared identity and reference tokens; registration failure disposes its moved payload; final Rust-owned release invokes the validated compiler destructor; VM callbacks, allocation and FFI correctness remain trusted boundaries",
            else:
              "Rustler 0.39 Rust-owned ResourceArc model: explicit registration precondition, distinct linear ownership tokens, shared immutable destructor-free payload and bounded reference count; inherited Resource callback flags modeled false; VM pins, custom callbacks, physical allocation and FFI unverified"
          )
      }
    else
      _ -> nil
    end
  end

  def type_models(calls, prefix) do
    if Enum.any?(calls, fn {_, m} -> m[:native_resource_type] end),
      do: [
        %{
          rust: Enum.join(@arc, "::"),
          lean: "Lynx.NativeResourceArc",
          import: hd(String.split(prefix, ".")) <> ".NativeRuntime",
          label:
            "Rust-owned ResourceArc identities and reference tokens; inherited Rustler 0.39 Resource flags are external false-constant models; registration is an explicit environment precondition, not a verified loader or BEAM resource codec"
        }
      ],
      else: []
  end

  def external_names(calls) do
    if Enum.any?(calls, fn {_, model} -> model[:native_resource_type] end) do
      %{
        "globals" =>
          Enum.map(~w(IMPLEMENTS_DESTRUCTOR IMPLEMENTS_DOWN), fn flag ->
            %{
              "rust_pattern" => "rustler::resource::traits::Resource::" <> flag,
              "extract_name" =>
                "Lynx.NativeResourceArc." <>
                  if(flag == "IMPLEMENTS_DESTRUCTOR",
                    do: "defaultDestructor",
                    else: "defaultDown"
                  ),
              "can_fail" => true
            }
          end)
      }
    else
      %{}
    end
  end

  defp identity?(f, "new", self, trait, _t, refs) do
    case f["item_meta"]["name"] do
      [
        a,
        b,
        c,
        %{
          "Impl" => %{
            "Ty" => %{"kind" => "InherentImplBlock", "params" => p, "skip_binder" => parent}
          }
        },
        %{"Ident" => ["new", 0]}
      ] ->
        [a, b, c] == path(~w(rustler resource arc)) and f["src"] == "Normal" and
          params?(p, 0, p["trait_clauses"]) and length(p["trait_clauses"]) == 1 and
          resource_clause?(hd(p["trait_clauses"]), trait, refs, %{
            "TypeVar" => %{"Bound" => [1, 0]}
          }) and
          CallModels.expand(parent, refs) ==
            put_in(self, ["Adt", "generics", "types"], [%{"TypeVar" => %{"Bound" => [0, 0]}}])

      _ ->
        false
    end
  end

  defp identity?(f, method, self, resource, t, refs) do
    with %{"TraitImpl" => %{"impl_ref" => %{"id" => impl_id}, "trait_ref" => %{"id" => trait}}} <-
           f["src"],
         impl when not is_nil(impl) <-
           Enum.find(t["trait_impls"], &(&1 && &1["def_id"] == impl_id)),
         decl when not is_nil(decl) <- Enum.find(t["trait_decls"], &(&1 && &1["def_id"] == trait)),
         true <-
           decl["item_meta"]["name"] ==
             path(if(method == "clone", do: ~w(core clone Clone), else: ~w(core ops deref Deref))),
         true <-
           impl["src"] == "Normal" and impl["is_unsafe"] == false and impl["is_negative"] == false,
         params = CallModels.expand(impl["generics"], refs),
         [clause] <- params["trait_clauses"],
         true <- params?(params, 0, [clause]) and resource_clause?(clause, resource, refs),
         true <-
           f["item_meta"]["name"] ==
             path(~w(rustler resource arc)) ++
               [%{"Impl" => %{"Trait" => impl_id}}] ++ path([method]),
         true <-
           CallModels.expand(impl["impl_trait"], refs) == %{
             "id" => trait,
             "generics" => args(if(method == "clone", do: [self], else: [self, variable()]))
           },
         true <-
           impl["consts"] == [] and impl["types"] == if(method == "clone", do: [], else: [nil]),
         true <- length(impl["methods"]) == if(method == "clone", do: 2, else: 1),
         true <- Enum.count(impl["methods"], &(not is_nil(&1))) == 1 do
      FormatModels.method_identity?(
        f,
        Map.update!(impl, "methods", &Enum.reject(&1, fn v -> is_nil(v) end)),
        trait,
        %{translated: t, refs: refs, traits: trait_references(t, %{})}
      )
    else
      _ -> false
    end
  end

  def resource_clause?(clause, id, refs, type \\ %{"TypeVar" => %{"Free" => 0}})

  def resource_clause?(
        %{
          "clause_id" => 0,
          "trait_" => %{
            "regions" => [],
            "outlives" => [],
            "skip_binder" => %{"id" => id, "generics" => a}
          }
        },
        id,
        refs,
        type
      ),
      do: CallModels.expand(a, refs) == args([type])

  def resource_clause?(_, _, _, _), do: false

  defp trait_references(%{"Value" => [id, %{"kind" => _, "trait_decl_ref" => _} = value]}, refs) do
    if Map.has_key?(refs, id) and refs[id] != value,
      do: raise(ArgumentError, "inconsistent LLBC shared trait identity")

    trait_references(value, Map.put(refs, id, value))
  end

  defp trait_references(map, refs) when is_map(map),
    do: Enum.reduce(Map.values(map), refs, &trait_references/2)

  defp trait_references(list, refs) when is_list(list),
    do: Enum.reduce(list, refs, &trait_references/2)

  defp trait_references(_, refs), do: refs

  def trait_references(translated), do: trait_references(translated, %{})

  def dictionary(%{"regions" => [], "outlives" => [], "skip_binder" => value}, refs),
    do: dictionary_value(value, refs)

  def dictionary(_, _), do: nil
  defp dictionary_value(%{"Value" => [_, value]}, _), do: value
  defp dictionary_value(%{"Deduplicated" => id}, refs), do: refs[id]
  defp dictionary_value(_, _), do: nil

  def params?(p, n, clauses, bounds \\ []) do
    match?(
      %{"types" => [%{"index" => 0}], "const_generics" => [], "trait_type_constraints" => []},
      p
    ) and
      length(p["regions"]) == n and
      Enum.all?(Enum.with_index(p["regions"]), fn {r, i} -> r["index"] == i end) and
      p["trait_clauses"] == clauses and p["outlives"] == bounds
  end

  defp method(f) do
    case List.last(f["item_meta"]["name"]) do
      %{"Ident" => [name, 0]} -> name
      _ -> nil
    end
  end

  defp path(p), do: Enum.map(p, &%{"Ident" => [&1, 0]})
  defp variable, do: %{"TypeVar" => %{"Free" => 0}}
  defp reference(t), do: %{"Ref" => [%{"Var" => %{"Free" => 0}}, t, "Shared"]}

  def args(types, traits \\ [], regions \\ []),
    do: %{"types" => types, "trait_refs" => traits, "regions" => regions, "const_generics" => []}

  defp adt(id, t), do: %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args([t])}}

  defp bound,
    do: %{
      "regions" => [],
      "outlives" => [],
      "skip_binder" => [%{"Lub" => variable()}, %{"Var" => %{"Free" => 0}}]
    }
end
