defmodule Lynx.Rust.NativeUnwindDrops do
  @moduledoc false
  alias Lynx.Rust.{LLBC, NativeDrops}
  @name [%{"Ident" => ["LynxCompilerUnwind", 0]}, %{"Ident" => ["drop", 0]}]

  # This declaration is a compiler adapter for a validated std destructor site,
  # not an extracted Rust implementation. Its model is always reported external.
  def prepare!(document) do
    functions = document["translated"]["fun_decls"]

    if Enum.any?(functions, &(&1 && hd(&1["item_meta"]["name"]) == hd(@name))),
      do: raise(ArgumentError, "reserved compiler unwind namespace already exists")

    if NativeDrops.needs_lowering?(document) do
      refs = LLBC.type_references!(document)

      source =
        Enum.find(
          functions,
          &(&1 && NativeDrops.consuming_function?(&1, document["translated"], refs))
        )

      unless source,
        do:
          raise(
            ArgumentError,
            "unwind destruction requires the actual core::mem::drop declaration"
          )

      helper =
        source
        |> Map.put("def_id", length(functions))
        |> put_in(["item_meta", "name"], @name)
        |> put_in(["item_meta", "is_local"], false)
        |> put_in(["item_meta", "started_from"], false)

      document = put_in(document, ["translated", "fun_decls"], functions ++ [helper])

      document =
        update_in(
          document,
          ["translated", "ordered_decls"],
          &[%{"Fun" => %{"NonRec" => helper["def_id"]}} | &1]
        )

      {document, helper}
    else
      {document, nil}
    end
  end

  def resolve(function, translated, refs) do
    with true <- function["item_meta"]["name"] == @name,
         %{"body" => "Opaque", "src" => "Normal"} <- function,
         source when not is_nil(source) <-
           Enum.find(
             translated["fun_decls"],
             &(&1 && NativeDrops.consuming_function?(&1, translated, refs))
           ),
         true <-
           function["signature"] == source["signature"] and
             function["generics"] == source["generics"],
         %{} = model <- NativeDrops.resolve(source, translated, refs) do
      Map.merge(model, %{
        rust_name: "LynxCompilerUnwind::drop",
        lean: "Lynx.NativeUnwindDrop.drop",
        native_unwind_dispose: true,
        label:
          "Compiler unwind adapter for validated std MutexGuard/Mutex destructor dictionaries; commits the latest borrowed guard payload, unlocks and poisons on panic, or disposes an unlocked mutex; nonpanicking entry and guard acquisition, including incoming guards, and no nested cleanup calls required; std, physical thread context, allocation and FFI correctness unverified"
      })
    else
      _ -> nil
    end
  end
end
