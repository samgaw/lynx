defmodule Lynx.Rust.OwnedStringModels do
  @moduledoc false
  alias Lynx.Rust.{CallModels, CollectionModels, LLBC, ResourceModels}

  def type?(type, translated, refs) do
    with %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => arguments}} <-
           CallModels.expand(type, refs),
         true <- arguments == args([]),
         declaration when not is_nil(declaration) <- find(translated["type_decls"], id) do
      string?(declaration) and empty?(declaration["generics"])
    else
      _ -> false
    end
  end

  def resolve(function, translated, refs) do
    function = CallModels.expand(function, refs)

    with %{
           "body" => "Opaque",
           "src" => "Normal",
           "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig,
           "generics" => params,
           "item_meta" => %{
             "name" => [
               %{"Ident" => ["alloc", 0]},
               %{"Ident" => ["string", 0]},
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
         true <- empty?(parent_params),
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}} <- parent,
         true <- args == args([]),
         type when not is_nil(type) <- find(translated["type_decls"], id),
         true <- empty?(type["generics"]) do
      cond do
        string?(type) ->
          string(method, parent, params, sig, translated, refs)

        error?(type, translated, refs) and method == "into_bytes" and empty?(params) and
          sig["inputs"] == [parent] and byte_vector?(sig["output"], translated, refs) ->
          model("FromUtf8Error", method, "errorIntoBytes", false)
          |> error_metadata(type, translated, refs)

        true ->
          nil
      end
    else
      _ -> nil
    end
  end

  defp string("from_utf8" = method, self, params, sig, translated, refs) do
    with true <- empty?(params),
         [input] <- sig["inputs"],
         true <- byte_vector?(input, translated, refs),
         %{"Adt" => %{"id" => result, "builtin" => nil, "generics" => result_args}} <-
           sig["output"],
         %{
           "types" => [
             ^self,
             %{"Adt" => %{"id" => error, "builtin" => nil, "generics" => error_args}}
           ]
         } <- result_args,
         true <- error_args == args([]),
         true <- result_args == args([self, adt(error)]),
         true <- LLBC.result_type?(result, %{translated: translated, references: refs}),
         error_type when not is_nil(error_type) <- find(translated["type_decls"], error),
         true <- error?(error_type, translated, refs) do
      model("String", method, "fromUtf8", true)
      |> error_metadata(error_type, translated, refs)
    else
      _ -> nil
    end
  end

  defp string("into_bytes" = method, self, params, sig, translated, refs) do
    if empty?(params) and sig["inputs"] == [self] and
         byte_vector?(sig["output"], translated, refs),
       do: model("String", method, "intoBytes", true)
  end

  defp string("push_str" = method, self, params, sig, translated, refs) do
    with true <- regions?(params, [0, 1]),
         [mut, %{"Ref" => [region, str, "Shared"]}] <- sig["inputs"],
         true <- mut == ref(0, self, "Mut") and region == region(1),
         true <- str?(str, translated, refs),
         true <-
           sig["output"] == %{"Adt" => %{"id" => 0, "builtin" => "Tuple", "generics" => args([])}} do
      model("String", method, "pushStr", true)
    else
      _ -> nil
    end
  end

  defp string(_, _, _, _, _, _), do: nil

  defp model(parent, method, lean, monadic) do
    %{
      rust_name: "alloc::string::{alloc::string::#{parent}}::#{method}",
      lean: "Lynx.OwnedString." <> lean,
      owned_string_op: lean,
      builtin: false,
      can_fail: monadic,
      lift: monadic,
      label:
        "Owned UTF-8 String model preserving bytes and failed-conversion ownership; canonical standard types/signatures validated; Rust alloc, native layout, allocation and reclamation remain unverified; append beyond 262144 bytes exhausts verification"
    }
  end

  defp string?(type),
    do:
      type["src"] == "Normal" and type["kind"] == "Opaque" and
        type["item_meta"]["name"] == path(~w(alloc string String)) and
        type["item_meta"]["lang_item"] == "String"

  defp error?(type, translated, refs) do
    with true <-
           type["src"] == "Normal" and
             type["item_meta"]["name"] == path(~w(alloc string FromUtf8Error)),
         true <- empty?(type["generics"]),
         %{"Struct" => [%{"name" => "bytes", "ty" => bytes}, %{"name" => "error", "ty" => error}]} <-
           type["kind"],
         true <- byte_vector?(bytes, translated, refs),
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => error_args}} <-
           CallModels.expand(error, refs),
         true <- error_args == args([]),
         inner when not is_nil(inner) <- find(translated["type_decls"], id),
         true <- inner["item_meta"]["name"] == path(~w(core str error Utf8Error)) do
      Lynx.Rust.BytesModels.error_type?(inner, translated, refs)
    else
      _ -> false
    end
  end

  defp error_metadata(model, type, _translated, refs) do
    [_, field] = type["kind"]["Struct"]
    %{"Adt" => %{"id" => inner}} = CallModels.expand(field["ty"], refs)
    model |> Map.put(:owned_utf8_error_type, type["def_id"]) |> Map.put(:bytes_error_type, inner)
  end

  defp byte_vector?(type, translated, refs),
    do:
      CollectionModels.scalar_vector_element(type, translated, refs) ==
        {:ok, %{"Scalar" => %{"Integer" => %{"Unsigned" => "U8"}}}}

  defp str?(
         %{"Adt" => %{"id" => id, "builtin" => "Str", "generics" => str_args}},
         translated,
         refs
       ) do
    with true <- str_args == args([]),
         %{
           "src" => %{"Builtin" => "Str"},
           "generics" => params,
           "kind" => %{"Struct" => [%{"ty" => field}]}
         } <- find(translated["type_decls"], id) do
      empty?(params) and
        CallModels.expand(field, refs) == %{
          "Slice" => [%{"Scalar" => %{"Integer" => %{"Unsigned" => "U8"}}}, nil]
        }
    else
      _ -> false
    end
  end

  defp str?(_, _, _), do: false

  defp empty?(params),
    do:
      is_map(params) and
        Enum.all?(
          ~w(regions types const_generics trait_clauses outlives trait_type_constraints),
          &(params[&1] == [])
        )

  defp regions?(params, indices),
    do:
      is_list(params["regions"]) and Enum.map(params["regions"], & &1["index"]) == indices and
        empty?(Map.put(params, "regions", []))

  defp find(rows, id), do: Enum.find(rows || [], &(&1 && &1["def_id"] == id))
  defp args(types), do: ResourceModels.args(types)
  defp adt(id), do: %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args([])}}
  defp region(index), do: %{"Var" => %{"Free" => index}}
  defp ref(index, type, kind), do: %{"Ref" => [region(index), type, kind]}
  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})

  def scope(audit, prefix) do
    %{
      audit
      | external_calls:
          Map.new(audit.external_calls, fn {id, model} ->
            if model[:owned_string_op],
              do: {id, %{model | lean: prefix <> ".OwnedString." <> model.owned_string_op}},
              else: {id, model}
          end)
    }
  end

  def install!(audit, translation, output, prefix) do
    models = for {_, m} <- audit.external_calls, m[:owned_string_op], do: m
    if models == [], do: [], else: install_models!(models, translation, output, prefix)
  end

  defp install_models!(models, translation, output, prefix) do
    module = prefix <> ".OwnedStringModel"
    path = Path.join(output, String.replace(module, ".", "/") <> ".lean")

    case File.read(path) do
      {:ok, "-- Generated by Lynx: owned UTF-8 String models.\n" <> _} -> :ok
      {:error, :enoent} -> :ok
      _ -> raise ArgumentError, "refusing to overwrite a user owned-string module: #{path}"
    end

    ids = for m <- models, m[:owned_utf8_error_type], do: m.owned_utf8_error_type

    error =
      case Enum.uniq(ids) do
        [] -> nil
        [id] -> Enum.find(translation["types"], &(&1["def_id"] == id))["lean_name"]
        _ -> raise ArgumentError, "inconsistent owned UTF-8 error definitions"
      end

    extra =
      if error do
        """
        @[expose] def fromUtf8 (input : alloc.vec.Vec U8) : RustM (core.result.Result String #{error}) := do
          let decoded ← #{prefix}.Bytes.fromUtf8 input.slice
          match decoded with
          | .Ok _ => match String.fromUTF8? (#{prefix}.Bytes.bytes input.slice) with
            | some text => .ok (.Ok text)
            | none => .fail .undef
          | .Err error => .ok (.Err ⟨input,error⟩)
        @[expose] def errorIntoBytes (error : #{error}) : alloc.vec.Vec U8 := error.bytes
        """
      else
        ""
      end

    source = """
    -- Generated by Lynx: owned UTF-8 String models.
    module
    public import #{prefix}.Types
    #{if error, do: "public import #{prefix}.BytesModel", else: ""}
    public section
    open Aeneas Aeneas.Std
    namespace #{prefix}.OwnedString
    @[expose] def byteList (text : String) : List U8 :=
      text.toByteArray.toList.map (fun byte => ⟨BitVec.ofNat 8 byte.toNat⟩)
    @[expose] def intoBytes (text : String) : RustM (alloc.vec.Vec U8) :=
      if bound : (byteList text).length ≤ Usize.max then .ok ⟨Slice.from (byteList text) bound⟩
      else .fail .undef
    @[expose] def pushStr (text : String) (suffix : Str) : RustM String :=
      match String.fromUTF8? ⟨(suffix.val.map (fun byte => UInt8.ofNat byte.val)).toArray⟩ with
      | none => .fail .undef
      | some suffix => if (text ++ suffix).toByteArray.size ≤ 262144 then .ok (text ++ suffix) else .fail .undef
    #{extra}
    end #{prefix}.OwnedString
    """

    File.mkdir_p!(Path.dirname(path))
    File.write!(path, source)
    funs = Path.join(output, String.replace(prefix, ".", "/") <> "/Funs.lean")
    marker = "public import " <> prefix <> ".Types"
    contents = File.read!(funs)

    unless String.contains?(contents, marker),
      do: raise(ArgumentError, "missing generated owned-string Types import")

    File.write!(funs, String.replace(contents, marker, marker <> "\npublic import " <> module))
    [module]
  end
end
