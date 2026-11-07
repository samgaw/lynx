defmodule Lynx.Rust.FileOpenModels do
  @moduledoc false
  alias Lynx.Rust.{CallModels, FileModels, LLBC, ResourceModels}

  # Erasing AsRef is justified only by the concrete standard &str dictionary.
  # Custom conversions, owned paths and generic unresolved callers stay closed.
  def resolve(f, t, refs),
    do: opening(f, t, refs) || renaming(f, t, refs) || conversion(f, t, refs)

  defp renaming(f, t, refs) do
    with %{
           "body" => "Opaque",
           "src" => "Normal",
           "generics" => p,
           "signature" => %{"abi" => "Rust", "is_unsafe" => false, "is_variadic" => false} = sig
         } <- f,
         true <- f["item_meta"]["name"] == name(~w(std fs rename)),
         true <- params?(p, 0, 2, 2) and p["outlives"] == [],
         path when not is_nil(path) <- named(t, "type_decls", ~w(std path Path)),
         true <- path["kind"] == "Opaque" and params?(path["generics"], 0, 0, 0),
         error when not is_nil(error) <- named(t, "type_decls", ~w(core io error Error)),
         trait when not is_nil(trait) <- named(t, "trait_decls", ~w(core convert AsRef)),
         true <- params?(trait["generics"], 0, 2, 0),
         true <- trait["types"] == [] and trait["consts"] == [] and length(trait["methods"]) == 1,
         [left, right] <- p["trait_clauses"],
         true <- clause?(left, trait["def_id"], [variable(0), adt(path["def_id"])], refs),
         true <- clause?(right, trait["def_id"], [variable(1), adt(path["def_id"])], refs, 1),
         true <- CallModels.expand(sig["inputs"], refs) == [variable(0), variable(1)],
         %{"Adt" => %{"id" => result, "builtin" => nil, "generics" => output}} <-
           CallModels.expand(sig["output"], refs),
         true <-
           output ==
             args([
               %{"Adt" => %{"id" => 0, "builtin" => "Tuple", "generics" => args([])}},
               adt(error["def_id"])
             ]),
         true <- LLBC.result_type?(result, %{translated: t, references: refs}) do
      %{
        rust_name: "std::fs::rename",
        lean: "Lynx.NativeFile.rename",
        builtin: false,
        can_fail: true,
        lift: true,
        keep_params: [false, false],
        keep_trait_clauses: [false, false],
        native_file_rename: {path["def_id"], trait["def_id"]},
        native_file_types: {nil, error["def_id"]},
        native_cutoff_only: true,
        label:
          "Bounded single-directory Unix-style atomic rename model: both concrete standard &str AsRef<Path> dictionaries validated; same-inode aliases are a no-op; replacement retains existing open inode capabilities; errors may leave the operation applied or unapplied; namespace changes are pending, not synchronized; atomicity, paths, filesystem/OS/FFI correspondence remain assumptions; directories, symlinks and unsupported path forms rejected"
      }
    else
      _ -> nil
    end
  end

  defp opening(f, t, refs) do
    with %{
           "body" => "Opaque",
           "src" => "Normal",
           "generics" => p,
           "signature" => %{"abi" => "Rust", "is_unsafe" => false, "is_variadic" => false} = sig
         } <- f,
         %{"def_id" => file} <- FileModels.declaration(t),
         path when not is_nil(path) <- named(t, "type_decls", ~w(std path Path)),
         true <- path["kind"] == "Opaque" and params?(path["generics"], 0, 0, 0),
         error when not is_nil(error) <- named(t, "type_decls", ~w(core io error Error)),
         trait when not is_nil(trait) <- named(t, "trait_decls", ~w(core convert AsRef)),
         true <- params?(trait["generics"], 0, 2, 0),
         true <- trait["types"] == [] and trait["consts"] == [] and length(trait["methods"]) == 1,
         true <- params?(p, 0, 1, 1) and p["outlives"] == [],
         [clause] <- p["trait_clauses"],
         true <- clause?(clause, trait["def_id"], [variable(0), adt(path["def_id"])], refs),
         [a, b, %{"Impl" => %{"Ty" => parent}}, %{"Ident" => [operation, 0]}] <-
           f["item_meta"]["name"],
         true <- operation in ["open", "create_new"],
         true <- [a, b] == name(~w(std fs)),
         true <- parent["kind"] == "InherentImplBlock" and params?(parent["params"], 0, 0, 0),
         true <- CallModels.expand(parent["skip_binder"], refs) == adt(file),
         true <- CallModels.expand(sig["inputs"], refs) == [variable(0)],
         %{"Adt" => %{"id" => result, "builtin" => nil, "generics" => out}} <-
           CallModels.expand(sig["output"], refs),
         true <- out == args([adt(file), adt(error["def_id"])]),
         true <- LLBC.result_type?(result, %{translated: t, references: refs}) do
      %{
        rust_name: "std::fs::{std::fs::File}::" <> operation,
        lean:
          "Lynx.NativeFile." <> if(operation == "open", do: "openReadOnly", else: "createNew"),
        builtin: false,
        can_fail: true,
        lift: true,
        keep_params: [false],
        keep_trait_clauses: [false],
        native_file_open: {path["def_id"], trait["def_id"]},
        native_file_types: {file, error["def_id"]},
        native_cutoff_only: true,
        label:
          "Bounded File::#{operation}<&str> model (1024 names and pending namespace snapshots): concrete standard AsRef<Path> dictionaries validated before erasure; shared inode contents and independent handle offsets; open grants read-only access; exclusive creation grants read/write access to a fresh empty inode and records a pending, unsynchronized namespace change; failed exclusive creation leaves namespace/inode contents unchanged (std/OS model assumption); explicit namespace and OS outcomes; std/path/OS/FFI correspondence unverified; custom AsRef, symlinks and unsupported path forms rejected"
      }
    else
      _ -> nil
    end
  end

  def audit(functions, models, t, refs) do
    traits = ResourceModels.trait_references(t)

    Enum.reduce_while(functions, {:ok, %{}}, fn f, {:ok, found} ->
      try do
        deps = calls!(f["body"], models, t, refs, traits)
        {:cont, {:ok, merge(found, deps)}}
      rescue
        e in ArgumentError -> {:halt, {:error, f, Exception.message(e)}}
      end
    end)
  end

  def type_models(calls, prefix) do
    if Enum.any?(calls, fn {_, m} -> m[:native_file_open] || m[:native_file_rename] end),
      do: [
        %{
          rust: "std::path::Path",
          lean: "Aeneas.Std.Str",
          import: hd(String.split(prefix, ".")) <> ".NativeRuntime",
          label:
            "Standard UTF-8 str-backed Path view; only validated standard AsRef<Path> chains may be erased; OS pathname correspondence unverified"
        }
      ],
      else: []
  end

  defp calls!(
         %{"Regular" => %{"kind" => %{"Fun" => id}, "generics" => g}},
         models,
         t,
         refs,
         traits
       ) do
    case models[id] do
      %{native_file_rename: {path, trait}} ->
        case g do
          %{
            "regions" => [],
            "types" => [left, right],
            "const_generics" => [],
            "trait_refs" => [a, b]
          } ->
            found =
              for {type, dict} <- [{left, a}, {right, b}] do
                call?(%{args([type]) | "trait_refs" => [dict]}, path, trait, t, refs, traits)
              end

            case found do
              [{:ok, x}, {:ok, y}] ->
                %{id => Enum.uniq(x ++ y)}

              _ ->
                raise ArgumentError,
                      "rename requires concrete standard &str AsRef<Path> implementations for both paths"
            end

          _ ->
            raise ArgumentError, "rename requires two concrete standard &str path arguments"
        end

      %{native_file_open: {path, trait}} ->
        case call?(g, path, trait, t, refs, traits) do
          {:ok, ids} ->
            %{id => ids}

          _ ->
            raise ArgumentError,
                  "File opening/creation requires the concrete standard &str AsRef<Path> implementation; custom or unresolved path conversions are unsupported"
        end

      _ ->
        %{}
    end
  end

  defp calls!(m, models, t, refs, traits) when is_map(m),
    do: calls!(Map.values(m), models, t, refs, traits)

  defp calls!(l, models, t, refs, traits) when is_list(l),
    do:
      Enum.reduce(l, %{}, fn node, found ->
        merge(found, calls!(node, models, t, refs, traits))
      end)

  defp calls!(_, _, _, _, _), do: %{}
  defp merge(a, b), do: Map.merge(a, b, fn _, x, y -> Enum.uniq(x ++ y) end)

  defp conversion(f, t, refs) do
    with %{"body" => "Opaque", "src" => %{"TraitImpl" => src}, "signature" => sig} <- f,
         impl when not is_nil(impl) <- find(t["trait_impls"], src["impl_ref"]["id"]),
         [selected] <- impl["methods"],
         true <- selected["skip_binder"]["id"] == f["def_id"],
         trait when not is_nil(trait) <- named(t, "trait_decls", ~w(core convert AsRef)),
         path when not is_nil(path) <- named(t, "type_decls", ~w(std path Path)) do
      tid = trait["def_id"]
      input = CallModels.expand(sig["inputs"], refs)
      output = CallModels.expand(sig["output"], refs)
      implementation_args = expand_args(impl["impl_trait"]["generics"], refs)
      string = List.first(implementation_args["types"])

      cond do
        standard_impl?(impl, tid, ~w(core convert), 1, 2, 1) and
          clause?(hd(impl["generics"]["trait_clauses"]), tid, [variable(0), variable(1)], refs) and
          expand_args(impl["impl_trait"]["generics"], refs) ==
            args([reference(0, variable(0)), variable(1)]) and
            method?(
              impl,
              tid,
              [reference(1, reference(0, variable(0)))],
              reference(1, variable(1)),
              t,
              refs
            ) ->
          %{
            rust_name: "core::convert::{core::convert::AsRef<&'0 @T, @U>}::as_ref",
            lean: "Lynx.NativeFile.asRefShared",
            builtin: false,
            can_fail: true,
            lift: true,
            label:
              "Standard shared-reference AsRef forwarding invokes the actual supplied conversion dictionary; Rust core implementation unverified"
          }

        standard_impl?(impl, tid, ~w(std path), 0, 0, 0) and
          str?(string) and implementation_args == args([string, adt(path["def_id"])]) and
          input == [reference(0, string)] and
          output == reference(0, adt(path["def_id"])) and
            method?(impl, tid, input, output, t, refs) ->
          %{
            rust_name: "std::path::{core::convert::AsRef<str, std::path::Path>}::as_ref",
            lean: "Lynx.NativeFile.asRefStr",
            builtin: false,
            can_fail: true,
            lift: true,
            label:
              "Standard str-to-Path borrowed view preserves bytes; Rust std/OS pathname correspondence unverified"
          }

        true ->
          nil
      end
    else
      _ -> nil
    end
  end

  defp call?(g, path, trait, t, refs, traits) do
    with %{"regions" => [], "const_generics" => [], "types" => [self], "trait_refs" => [dict]} <-
           g,
         %{"Ref" => [region, string, "Shared"]} = self <- CallModels.expand(self, refs),
         true <- str?(string),
         %{"kind" => %{"TraitImpl" => %{"id" => id, "generics" => ig}}, "trait_decl_ref" => decl} <-
           ResourceModels.dictionary(dict, traits),
         true <-
           decl["id"] == trait and expand_args(decl["generics"], refs) == args([self, adt(path)]),
         %{
           "regions" => [^region],
           "types" => [s, p],
           "const_generics" => [],
           "trait_refs" => [child]
         } <- ig,
         true <- CallModels.expand([s, p], refs) == [string, adt(path)],
         impl when not is_nil(impl) <- find(t["trait_impls"], id),
         true <- standard_impl?(impl, trait, ~w(core convert), 1, 2, 1),
         true <-
           expand_args(impl["impl_trait"]["generics"], refs) ==
             args([reference(0, variable(0)), variable(1)]),
         [clause] <- impl["generics"]["trait_clauses"],
         true <- clause?(clause, trait, [variable(0), variable(1)], refs),
         true <-
           method?(
             impl,
             trait,
             [reference(1, reference(0, variable(0)))],
             reference(1, variable(1)),
             t,
             refs
           ),
         %{"kind" => %{"TraitImpl" => %{"id" => sid, "generics" => sg}}, "trait_decl_ref" => sd} <-
           ResourceModels.dictionary(child, traits),
         true <- sg == args([]),
         true <-
           sd["id"] == trait and expand_args(sd["generics"], refs) == args([string, adt(path)]),
         specific when not is_nil(specific) <- find(t["trait_impls"], sid),
         true <- standard_impl?(specific, trait, ~w(std path), 0, 0, 0),
         true <-
           expand_args(specific["impl_trait"]["generics"], refs) == args([string, adt(path)]),
         true <-
           method?(specific, trait, [reference(0, string)], reference(0, adt(path)), t, refs) do
      {:ok,
       [hd(impl["methods"])["skip_binder"]["id"], hd(specific["methods"])["skip_binder"]["id"]]}
    else
      _ -> false
    end
  end

  defp standard_impl?(
         %{"src" => "Normal", "is_unsafe" => false, "is_negative" => false} = impl,
         trait,
         prefix,
         regions,
         types,
         clauses
       ) do
    impl["item_meta"]["name"] == name(prefix) ++ [%{"Impl" => %{"Trait" => impl["def_id"]}}] and
      impl["impl_trait"]["id"] == trait and params?(impl["generics"], regions, types, clauses) and
      impl["types"] == [] and impl["consts"] == [] and impl["implied_trait_refs"] == []
  end

  defp standard_impl?(_, _, _, _, _, _), do: false

  defp method?(impl, trait, input, output, t, refs) do
    with [%{"kind" => %{"TraitMethod" => [^trait, 0]}, "skip_binder" => ptr}] <- impl["methods"],
         f when not is_nil(f) <- find(t["fun_decls"], ptr["id"]),
         %{"body" => "Opaque", "src" => %{"TraitImpl" => src}, "signature" => sig} <- f,
         true <-
           src["impl_ref"]["id"] == impl["def_id"] and src["trait_ref"]["id"] == trait and
             src["item_id"] == 0 and src["reuses_default"] == false,
         true <- f["item_meta"]["name"] == impl["item_meta"]["name"] ++ name(["as_ref"]),
         true <-
           sig["abi"] == "Rust" and sig["is_unsafe"] == false and sig["is_variadic"] == false,
         true <-
           params?(
             f["generics"],
             length(impl["generics"]["regions"]) + 1,
             length(impl["generics"]["types"]),
             length(impl["generics"]["trait_clauses"])
           ),
         true <-
           CallModels.expand(sig["inputs"], refs) == input and
             CallModels.expand(sig["output"], refs) == output do
      true
    else
      _ -> false
    end
  end

  defp clause?(clause, trait, types, refs, index \\ 0)

  defp clause?(
         %{
           "clause_id" => index,
           "trait_" => %{"regions" => [], "outlives" => [], "skip_binder" => decl}
         },
         trait,
         types,
         refs,
         expected
       ),
       do:
         index == expected and decl["id"] == trait and
           expand_args(decl["generics"], refs) == args(types)

  defp clause?(_, _, _, _, _), do: false

  defp params?(p, regions, types, clauses),
    do:
      is_map(p) and is_list(p["regions"]) and length(p["regions"]) == regions and
        is_list(p["types"]) and
        Enum.map(p["types"], & &1["index"]) == Enum.to_list(0..(types - 1)//1) and
        p["const_generics"] == [] and is_list(p["trait_clauses"]) and
        length(p["trait_clauses"]) == clauses and p["trait_type_constraints"] == []

  defp expand_args(g, refs), do: Map.update!(g, "types", &CallModels.expand(&1, refs))
  defp str?(%{"Adt" => %{"builtin" => "Str", "generics" => g}}), do: g == args([])
  defp str?(_), do: false

  defp named(t, key, parts) do
    case Enum.filter(t[key], &(&1 && &1["item_meta"]["name"] == name(parts))) do
      [item] -> item
      _ -> nil
    end
  end

  defp find(items, id) do
    case Enum.filter(items, &(&1 && &1["def_id"] == id)) do
      [item] -> item
      _ -> nil
    end
  end

  defp name(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})

  defp args(types),
    do: %{"types" => types, "regions" => [], "const_generics" => [], "trait_refs" => []}

  defp adt(id), do: %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args([])}}
  defp variable(i), do: %{"TypeVar" => %{"Free" => i}}
  defp reference(i, ty), do: %{"Ref" => [%{"Var" => %{"Free" => i}}, ty, "Shared"]}
end
