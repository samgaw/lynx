defmodule Lynx.Rustler.ErrorLiterals do
  @moduledoc false
  alias Lynx.Rust.{CallModels, Constants, LLBCJson}

  # Resolve only same-block literal loads/copies. Calls, control flow, drops,
  # borrows of other places and indirect writes are barriers; never infer that
  # an earlier assignment survived an aliasing mutation.
  def read(operand, prefix, ctx) do
    with %{} = place <- operand["Move"] || operand["Copy"],
         {:ok, element} <- shared_string(place["ty"], ctx.refs),
         %{"Local" => id} <- place["kind"],
         {:ok, text} <- local(id, prefix, element, ctx),
         true <- byte_size(text) <= 255 and Enum.all?(:binary.bin_to_list(text), &(&1 < 128)) do
      {:ok, text}
    else
      _ -> :error
    end
  end

  def static_string?(type, refs) do
    case CallModels.expand(type, refs) do
      %{"Ref" => ["Static", %{"Adt" => %{"builtin" => "Str", "generics" => args}}, "Shared"]} ->
        Constants.empty_arguments?(args)

      _ ->
        false
    end
  end

  # MIR can shorten a literal's reference lifetime to a body region. Its
  # provenance, rather than that shortened lifetime, establishes immutability.
  defp shared_string(type, refs) do
    case CallModels.expand(type, refs) do
      %{"Ref" => [_, %{"Adt" => %{"builtin" => "Str", "generics" => args}} = element, "Shared"]} ->
        if Constants.empty_arguments?(args), do: {:ok, element}, else: :error

      _ ->
        :error
    end
  end

  defp local(id, prefix, element, ctx) do
    prefix
    |> Enum.with_index()
    |> Enum.reverse()
    |> Enum.reduce_while(:error, fn {statement, index}, _ ->
      before = Enum.take(prefix, index)

      case statement["kind"] do
        %{"Assign" => [%{"kind" => %{"Local" => ^id}, "ty" => type}, value]} ->
          result =
            with {:ok, ^element} <- shared_string(type, ctx.refs) do
              value(value, before, element, ctx)
            else
              _ -> :error
            end

          {:halt, result}

        %{"Assign" => [%{"kind" => %{"Local" => _}}, %{"Use" => _}]} ->
          {:cont, :error}

        %{"StorageLive" => other} when other != id ->
          {:cont, :error}

        %{"StorageDead" => other} when other != id ->
          {:cont, :error}

        "Nop" ->
          {:cont, :error}

        _ ->
          {:halt, :error}
      end
    end)
  end

  defp value(%{"Use" => [operand, _]}, prefix, element, ctx) do
    with %{} = place <- operand["Move"] || operand["Copy"],
         {:ok, ^element} <- shared_string(place["ty"], ctx.refs),
         %{"Local" => id} <- place["kind"] do
      local(id, prefix, element, ctx)
    else
      _ -> :error
    end
  end

  defp value(
         %{"Ref" => %{"kind" => "Shared", "place" => place, "ptr_metadata" => metadata}},
         _prefix,
         element,
         ctx
       ) do
    with %{"Global" => %{"id" => id, "generics" => args}} <- place["kind"],
         true <- Constants.empty_arguments?(args),
         [%{"global_kind" => "AnonConst"} = global] <-
           Enum.filter(ctx.globals, &(&1["def_id"] == id)),
         false <- global["item_meta"]["has_errors"],
         %{"Value" => [_, [%{"Str" => text}, type]]} <- global["value"],
         true <- is_binary(text),
         true <- CallModels.expand(type, ctx.refs) == CallModels.expand(global["ty"], ctx.refs),
         true <- CallModels.expand(global["ty"], ctx.refs) == element,
         true <-
           CallModels.expand(place["ty"], ctx.refs) == CallModels.expand(global["ty"], ctx.refs),
         %{
           "Const" => %{
             "Value" => [_, [%{"Integer" => %{"Unsigned" => ["Usize", length]}}, length_type]]
           }
         } <- LLBCJson.restore_constant_references!(metadata, ctx.document),
         true <-
           CallModels.expand(length_type, ctx.refs) == %{
             "Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}
           },
         true <- length == Integer.to_string(byte_size(text)) do
      Constants.audit!([global], [], ctx.refs, ctx.types)
      {:ok, text}
    else
      _ -> :error
    end
  rescue
    ArgumentError -> :error
  end

  defp value(_, _, _, _), do: :error
end
