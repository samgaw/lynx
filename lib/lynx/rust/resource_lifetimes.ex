defmodule Lynx.Rust.ResourceLifetimes do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LLBC, NativeDrops, ResourceModels, RwLockModels}

  # A no-drop Rust payload can still own logical cells used to interpret aliasing.
  # Retire those cells at ownership end, without inventing a Rust destructor.
  def enabled?(translated) do
    if get_in(translated, ["options", "owned_drops"]) == true do
      false
    else
      resource =
        Enum.find(translated["trait_decls"] || [], fn trait ->
          trait &&
            trait["item_meta"]["name"] ==
              Enum.map(~w(rustler resource traits Resource), &%{"Ident" => [&1, 0]})
        end)

      if resource do
        refs = LLBC.type_references!(%{"translated" => translated})

        Enum.any?(translated["trait_impls"] || [], fn impl ->
          with %{"impl_trait" => %{"id" => id, "generics" => args}} <- impl,
               true <- id == resource["def_id"],
               %{"types" => [payload]} <- CallModels.expand(args, refs) do
            NativeDrops.destructor_free?(payload, translated, refs) and
              owned_cells?(payload, translated, refs, [])
          else
            _ -> false
          end
        end)
      else
        false
      end
    end
  end

  defp owned_cells?(type, translated, refs, seen) do
    case CallModels.expand(type, refs) do
      %{"Adt" => %{"id" => id}} ->
        declaration = Enum.find(translated["type_decls"], &(&1 && &1["def_id"] == id))

        cond do
          RwLockModels.type?(declaration) ->
            true

          id in seen ->
            false

          match?(%{"kind" => %{"Struct" => _}}, declaration) ->
            Enum.any?(
              declaration["kind"]["Struct"],
              &owned_cells?(&1["ty"], translated, refs, [id | seen])
            )

          true ->
            false
        end

      _ ->
        false
    end
  end

  def cleanup_fields!(type, audit) do
    unless NativeDrops.destructor_free?(
             %{
               "Adt" => %{
                 "id" => type["def_id"],
                 "builtin" => nil,
                 "generics" => ResourceModels.args([])
               }
             },
             audit.translated,
             audit.references
           ),
           do:
             raise(
               ArgumentError,
               "logical resource retirement requires a compiler-certified no-drop struct"
             )

    for field <- type["kind"]["Struct"],
        operation = field_cleanup!(CallModels.expand(field["ty"], audit.references), audit),
        operation != nil,
        do: {field["name"], operation}
  end

  defp field_cleanup!(%{"Scalar" => _} = scalar, audit) do
    unless NativeDrops.destructor_free?(scalar, audit.translated, audit.references),
      do: raise(ArgumentError, "unsupported logical resource scalar")

    nil
  end

  defp field_cleanup!(%{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}}, audit) do
    type = Enum.find(audit.translated["type_decls"], &(&1 && &1["def_id"] == id))

    cond do
      RwLockModels.type?(type) ->
        with %{"types" => [payload]} <- args,
             true <- args == ResourceModels.args([payload]),
             %{"Scalar" => _} = scalar <- CallModels.expand(payload, audit.references),
             true <- NativeDrops.destructor_free?(scalar, audit.translated, audit.references) do
          "NativeRwLock.dispose"
        else
          _ ->
            raise ArgumentError,
                  "logical resource RwLock retirement currently requires a primitive payload"
        end

      args == ResourceModels.args([]) and match?(%{"kind" => %{"Struct" => _}}, type) ->
        "NativeResourceCleanup.cleanup"

      true ->
        raise ArgumentError, "unsupported logical resource field ownership"
    end
  end

  defp field_cleanup!(_, _), do: raise(ArgumentError, "unsupported logical resource field")
end
