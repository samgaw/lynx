defmodule Lynx.Rustler.DecoderModels do
  @moduledoc false
  alias Lynx.Rust.{CallModels, FormatModels, LLBC}

  def resolve(%{"body" => "Opaque"} = function, translated, refs) do
    ctx = %{translated: translated, refs: refs, traits: %{}}
    self = %{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}}

    with %{"TraitImpl" => %{"impl_ref" => %{"id" => impl_id}}} <- function["src"],
         true <-
           function["item_meta"]["name"] ==
             path(~w(rustler types primitive)) ++
               [%{"Impl" => %{"Trait" => impl_id}}, %{"Ident" => ["decode", 0]}],
         true <- method?(function, self, ctx) do
      %{
        rust_name: "rustler::types::primitive::{rustler::types::Decoder<'_, u64>}::decode",
        lean: "Lynx.Rustler.Decoding.u64",
        builtin: false,
        can_fail: true,
        lift: false,
        label:
          "Rustler u64 Decoder FFI model with exact integer bounds and forwarded BadArg outcome; native Term handles and Rustler implementation unverified"
      }
    else
      _ -> nil
    end
  end

  def resolve(_, _, _), do: nil

  def binding!(id, audit, translation) do
    ctx = %{translated: audit.translated, refs: audit.references, traits: %{}}
    self = adt(id)
    candidates = Enum.filter(audit.functions, &method?(&1, self, ctx))

    with [function] <- candidates,
         true <- is_map(function["body"]),
         [%{"is_opaque" => false, "lean_name" => decoder}] <-
           Enum.filter(translation["functions"], &(&1["def_id"] == function["def_id"])),
         [%{"lean_name" => type}] <- Enum.filter(translation["types"], &(&1["def_id"] == id)) do
      %{"lean" => type, "decoder" => decoder, "decoder_definition_id" => function["def_id"]}
    else
      _ ->
        raise ArgumentError,
              "missing, opaque or mismatched first-party Rustler Decoder for argument type #{id}"
    end
  end

  # An opaque foreign Error may be forwarded from an admitted primitive, but
  # none of its constructors, payload projections or discriminants are modeled.
  # In particular, never treat every Rustler Error as BadArg.
  def audit(functions, translated, refs) do
    case named(translated, ~w(rustler error Error)) do
      nil ->
        {:ok, %{}}

      type ->
        case Enum.find(functions, &unsupported?(&1["body"], type["def_id"], refs)) do
          nil ->
            {:ok, %{}}

          function ->
            {:error, function,
             "Rustler Error construction or inspection requires unsupported dynamic-payload semantics; only opaque primitive-error forwarding is supported"}
        end
    end
  end

  defp method?(function, self, ctx) do
    with %{"TraitImpl" => %{"impl_ref" => %{"id" => impl_id}, "trait_ref" => %{"id" => trait}}} <-
           function["src"],
         %{} = impl <- declaration(ctx, "trait_impls", impl_id),
         true <- trait?(trait, ctx),
         true <-
           impl["src"] == "Normal" and impl["is_negative"] == false and impl["is_unsafe"] == false,
         true <- impl["consts"] == [] and impl["types"] == [] and impl["implied_trait_refs"] == [],
         true <- params?(impl["generics"], 1, 0) and params?(function["generics"], 1, 0),
         true <-
           CallModels.expand(impl["impl_trait"], ctx.refs) ==
             %{"id" => trait, "generics" => args([self], [region()])},
         true <- signature?(function["signature"], self, ctx),
         true <- FormatModels.method_identity?(function, impl, trait, ctx) do
      true
    else
      _ -> false
    end
  end

  defp trait?(id, ctx) do
    with %{
           "item_meta" => %{"name" => name},
           "is_unsafe" => false,
           "consts" => [],
           "types" => [],
           "implied_clauses" => [],
           "generics" => params,
           "methods" => [
             %{
               "kind" => %{"TraitMethod" => [^id, 0]},
               "params" => method,
               "skip_binder" => %{"name" => "decode", "signature" => sig, "default" => nil}
             }
           ]
         } <- declaration(ctx, "trait_decls", id) do
      name == path(~w(rustler types Decoder)) and
        params?(%{params | "outlives" => []}, 1, 1) and
        CallModels.expand(params["outlives"], ctx.refs) == [
          %{
            "regions" => [],
            "outlives" => [],
            "skip_binder" => [%{"Lub" => %{"TypeVar" => %{"Free" => 0}}}, region()]
          }
        ] and
        params?(method, 0, 0) and signature?(sig, %{"TypeVar" => %{"Free" => 0}}, ctx)
    else
      _ -> false
    end
  end

  defp signature?(sig, self, ctx) do
    with %{"kind" => "Opaque", "def_id" => term} <- named(ctx.translated, ~w(rustler term Term)),
         %{"kind" => "Opaque", "def_id" => error} <-
           named(ctx.translated, ~w(rustler error Error)),
         %{"def_id" => result} <- named(ctx.translated, ~w(core result Result)),
         true <- LLBC.result_type?(result, %{translated: ctx.translated, references: ctx.refs}) do
      CallModels.expand(sig, ctx.refs) == %{
        "is_unsafe" => false,
        "abi" => "Rust",
        "is_variadic" => false,
        "inputs" => [adt(term, [], [region()])],
        "output" => adt(result, [self, adt(error)])
      }
    else
      _ -> false
    end
  end

  defp unsupported?(%{"Aggregate" => [%{"Adt" => [%{"id" => id}, _, _]}, _]}, id, _refs), do: true

  defp unsupported?(%{"Discriminant" => place}, id, refs),
    do: error_place?(place, id, refs) or unsupported?(place, id, refs)

  defp unsupported?(%{"Match" => [place | rest]}, id, refs),
    do: error_place?(place, id, refs) or unsupported?(rest, id, refs)

  defp unsupported?(%{"kind" => %{"Projection" => [base, %{"Field" => _}]}}, id, refs),
    do: error_place?(base, id, refs) or unsupported?(base, id, refs)

  defp unsupported?(map, id, refs) when is_map(map),
    do: Enum.any?(Map.values(map), &unsupported?(&1, id, refs))

  defp unsupported?(list, id, refs) when is_list(list),
    do: Enum.any?(list, &unsupported?(&1, id, refs))

  defp unsupported?(_, _, _), do: false
  defp error_place?(%{"ty" => type}, id, refs), do: CallModels.expand(type, refs) == adt(id)
  defp error_place?(_, _, _), do: false

  defp params?(params, regions, types) do
    Enum.map(params["regions"], & &1["index"]) == indices(regions) and
      Enum.map(params["types"], & &1["index"]) == indices(types) and
      Enum.all?(
        ~w(const_generics trait_clauses outlives trait_type_constraints),
        &(params[&1] == [])
      )
  end

  defp indices(0), do: []
  defp indices(n), do: Enum.to_list(0..(n - 1))
  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})
  defp region, do: %{"Var" => %{"Free" => 0}}

  defp args(types, regions),
    do: %{"regions" => regions, "types" => types, "const_generics" => [], "trait_refs" => []}

  defp adt(id, types \\ [], regions \\ []),
    do: %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args(types, regions)}}

  defp declaration(ctx, key, id), do: Enum.find(ctx.translated[key], &(&1 && &1["def_id"] == id))

  defp named(translated, name),
    do: Enum.find(translated["type_decls"], &(&1 && &1["item_meta"]["name"] == path(name)))
end
