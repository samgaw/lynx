defmodule Lynx.Rust.NativePanicCapture do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LLBC, ResourceModels}
  @name Enum.map(~w(LynxCompilerCapture resource_new), &%{"Ident" => [&1, 0]})

  # Only this closed external constructor is adapted. Actual first-party bodies
  # and their original cleanup edges remain the responsibility of CapturedUnwind.
  def prepare!(document) do
    t = document["translated"]

    if Enum.any?(t["fun_decls"], &(&1 && hd(&1["item_meta"]["name"]) == hd(@name))),
      do: raise(ArgumentError, "reserved compiler panic capture namespace already exists")

    refs = LLBC.type_references!(document)

    sources =
      Enum.filter(t["fun_decls"], fn f ->
        f && match?(%{resource_operation: "new"}, ResourceModels.resolve(f, t, refs))
      end)

    case sources do
      [] -> document
      [source] -> insert(document, source)
      _ -> raise ArgumentError, "ambiguous compiler resource constructor capture"
    end
  end

  defp insert(document, source) do
    t = document["translated"]

    [result] =
      Enum.filter(
        t["type_decls"],
        &(&1 && &1["item_meta"]["name"] == path(~w(core result Result)))
      )

    next = max_ref(document) + 1

    unit = %{
      "Value" => [
        next,
        %{"Adt" => %{"builtin" => "Tuple", "id" => 0, "generics" => ResourceModels.args([])}}
      ]
    }

    output = %{
      "Value" => [
        next + 1,
        %{
          "Adt" => %{
            "id" => result["def_id"],
            "builtin" => nil,
            "generics" => ResourceModels.args([source["signature"]["output"], unit])
          }
        }
      ]
    }

    helper =
      source
      |> Map.put("def_id", length(t["fun_decls"]))
      |> put_in(["item_meta", "name"], @name)
      |> put_in(["item_meta", "is_local"], false)
      |> put_in(["item_meta", "started_from"], false)
      |> put_in(["signature", "output"], output)

    document
    |> put_in(["translated", "fun_decls"], t["fun_decls"] ++ [helper])
    |> update_in(
      ["translated", "ordered_decls"],
      &[%{"Fun" => %{"NonRec" => helper["def_id"]}} | &1]
    )
  end

  def resolve(%{"item_meta" => %{"name" => @name}} = helper, t, refs) do
    sources =
      for f <- t["fun_decls"],
          f != nil,
          model = ResourceModels.resolve(f, t, refs),
          model && model.resource_operation == "new",
          do: {f, model}

    with false <- get_in(t, ["options", "owned_drops"]) == true,
         [{source, model}] <- sources,
         "Opaque" <- helper["body"],
         "Normal" <- helper["src"],
         true <- helper["generics"] == source["generics"],
         true <-
           Map.delete(helper["signature"], "output") == Map.delete(source["signature"], "output"),
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}} <-
           CallModels.expand(helper["signature"]["output"], refs),
         true <- LLBC.result_type?(id, %{translated: t, references: refs}),
         %{"types" => [output, unit]} <- args,
         true <- args == ResourceModels.args([output, unit]),
         true <- output == CallModels.expand(source["signature"]["output"], refs),
         true <-
           unit == %{
             "Adt" => %{"builtin" => "Tuple", "id" => 0, "generics" => ResourceModels.args([])}
           } do
      Map.merge(model, %{
        rust_name: "LynxCompilerCapture::resource_new",
        lean:
          if(Lynx.Rust.ResourceLifetimes.enabled?(t),
            do: "Lynx.NativeResourceArc.newManagedCaptured",
            else: "Lynx.NativeResourceArc.newCaptured"
          ),
        native_cutoff_only: true,
        native_captured_source: source["def_id"],
        native_captured_source_name: model.rust_name,
        label:
          "Compiler capture adapter for the validated Rustler ResourceArc::new model: registration panic becomes an explicit exceptional result before caller cleanup; only destructor-free default Resource payloads admitted; exhaustion remains uncatchable; Rustler, allocation, native unwinding and FFI correctness unverified"
      })
    else
      _ -> nil
    end
  end

  def resolve(_, _, _), do: nil
  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})
  defp max_ref(%{"Value" => [id, value]}), do: max(id, max_ref(value))
  defp max_ref(map) when is_map(map), do: max_ref(Map.values(map))
  defp max_ref(list) when is_list(list), do: Enum.reduce(list, 0, &max(max_ref(&1), &2))
  defp max_ref(_), do: 0
end
