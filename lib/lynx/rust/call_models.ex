defmodule Lynx.Rust.CallModels do
  @moduledoc false

  # This catalogue is intentionally closed. These are explicitly reported
  # models, never proofs of foreign function implementations.
  def resolve(functions, translated, refs, enabled, execution \\ :pure) do
    for key <- enabled,
        key not in [
          :rustler_binary_as_slice,
          :rustler_encoders,
          :rustler_decoders,
          :native_wakers,
          :native_files,
          :captured_unwind_drops
        ],
        do: raise(ArgumentError, "unknown external Rust call model: #{inspect(key)}")

    for function <- functions,
        model =
          if(execution == :runtime,
            do:
              Lynx.Rust.ResultModels.resolve_native_expect(function, translated, refs) ||
                Lynx.Rust.OptionModels.resolve(function, translated, refs) ||
                if(:native_wakers in enabled,
                  do: Lynx.Rust.FutureModels.resolve(function, translated, refs)
                ) ||
                if(:native_files in enabled,
                  do:
                    Lynx.Rust.ResultModels.resolve_unused_io_debug(function, translated, refs) ||
                      Lynx.Rust.FileModels.resolve(function, translated, refs) ||
                      Lynx.Rust.FileOpenModels.resolve(function, translated, refs) ||
                      Lynx.Rust.FileDrops.resolve(function, translated, refs)
                ) ||
                Lynx.Rust.MutexModels.resolve(function, translated, refs) ||
                Lynx.Rust.RwLockModels.resolve(function, translated, refs) ||
                Lynx.Rust.ResourceModels.resolve(function, translated, refs) ||
                Lynx.Rust.LockModels.resolve(function, translated, refs) ||
                Lynx.Rust.PoisonModels.resolve(function, translated, refs) ||
                Lynx.Rust.GuardModels.resolve(function, translated, refs) ||
                Lynx.Rust.NativeDrops.resolve(function, translated, refs) ||
                if(:captured_unwind_drops in enabled,
                  do:
                    Lynx.Rust.NativeUnwindDrops.resolve(function, translated, refs) ||
                      Lynx.Rust.NativePanicCapture.resolve(function, translated, refs)
                )
          ) ||
            Lynx.Rust.BoxModels.resolve(function, translated, refs) ||
            Lynx.Rust.ResultModels.resolve(function, translated, refs) ||
            Lynx.Rust.TryModels.resolve(function, translated, refs) ||
            Lynx.Rust.SliceModels.resolve(function, translated, refs) ||
            Lynx.Rust.ArrayModels.resolve(function, translated, refs) ||
            Lynx.Rust.IndexModels.resolve(function, translated, refs) ||
            Lynx.Rust.ComparisonModels.resolve(function, translated, refs) ||
            Lynx.Rust.CollectionModels.resolve(function, translated, refs) ||
            Lynx.Rust.IteratorModels.resolve(function, translated, refs) ||
            Lynx.Rust.EndianModels.resolve(function, translated, refs) ||
            Lynx.Rust.StringModels.resolve(function, translated, refs) ||
            Lynx.Rust.BytesModels.resolve(function, translated, refs) ||
            Lynx.Rust.FormatModels.resolve(function, translated, refs) ||
            if(:rustler_encoders in enabled,
              do: Lynx.Rustler.EncoderModels.resolve(function, translated, refs)
            ) ||
            if(:rustler_decoders in enabled,
              do:
                Lynx.Rustler.ResultConversions.resolve(function, translated, refs) ||
                  Lynx.Rustler.DecoderModels.resolve(function, translated, refs) ||
                  Lynx.Rustler.AtomModels.resolve(function, translated, refs)
            ) ||
            match_function(function, translated, refs, enabled),
        model != nil,
        into: %{} do
      {function["def_id"],
       Map.merge(model, %{
         definition_id: function["def_id"],
         implementation_verified: false,
         status: :modelled,
         function: function
       })}
    end
  end

  defp match_function(
         %{
           "body" => "Opaque",
           "signature" =>
             %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = signature,
           "item_meta" => %{"name" => name},
           "generics" => generics
         },
         translated,
         refs,
         enabled
       ) do
    if candidate?(name, enabled) do
      inputs = Enum.map(signature["inputs"], &expand(&1, refs))
      output = expand(signature["output"], refs)

      case {name, inputs, output} do
        {[%{"Ident" => ["core", 0]}, %{"Ident" => ["mem", 0]}, %{"Ident" => ["replace", 0]}],
         [%{"Ref" => [%{"Var" => %{"Free" => 0}}, variable, "Mut"]}, variable], variable} ->
          if variable == %{"TypeVar" => %{"Free" => 0}} and generic_shape?(generics, 1, 1) do
            %{
              rust_name: "core::mem::replace",
              lean: "Aeneas.Std.core.mem.replace",
              builtin: true,
              can_fail: false,
              lift: false,
              native_replace: true,
              label:
                "Aeneas mutable replacement primitive; returns the previous owned value and reconstructs the borrow with its replacement; Rust core implementation not verified"
            }
          end

        {[
           %{"Ident" => ["core", 0]},
           %{"Ident" => ["num", 0]},
           %{"Impl" => %{"Ty" => %{"skip_binder" => parent}}},
           %{"Ident" => [operation, 0]}
         ], [scalar, scalar], %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}}}
        when operation in ["checked_add", "checked_mul"] ->
          width =
            case scalar do
              %{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}} -> "U64"
              %{"Scalar" => %{"Integer" => %{"Signed" => "I64"}}} -> "I64"
              _ -> nil
            end

          if is_binary(width) and parent_type(parent, refs) == scalar and
               generic_shape?(generics, 0, 0) and
               args == %{
                 "regions" => [],
                 "types" => [scalar],
                 "const_generics" => [],
                 "trait_refs" => []
               } and
               Enum.any?(translated["type_decls"], fn type ->
                 type && type["def_id"] == id &&
                   type["item_meta"]["name"] ==
                     [
                       %{"Ident" => ["core", 0]},
                       %{"Ident" => ["option", 0]},
                       %{"Ident" => ["Option", 0]}
                     ] &&
                   match?(
                     %{
                       "Enum" => [
                         %{
                           "id" => 0,
                           "name" => "None",
                           "fields" => [],
                           "discriminant" => %{"Signed" => ["Isize", "0"]}
                         },
                         %{
                           "id" => 1,
                           "name" => "Some",
                           "fields" => [_],
                           "discriminant" => %{"Signed" => ["Isize", "1"]}
                         }
                       ]
                     },
                     type["kind"]
                   ) &&
                   expand(hd(Enum.at(type["kind"]["Enum"], 1)["fields"])["ty"], refs) == %{
                     "TypeVar" => %{"Free" => 0}
                   }
               end) do
            %{
              rust_name: "core::num::{#{String.downcase(width)}}::#{operation}",
              lean: "Aeneas.Std.#{width}.#{operation}",
              builtin: true,
              can_fail: false,
              lift: true,
              label:
                "Aeneas #{String.downcase(width)} #{operation} model; overflow returns None; Rust core implementation not verified"
            }
          end

        {[
           %{"Ident" => ["core", 0]},
           %{"Ident" => ["num", 0]},
           %{"Impl" => %{"Ty" => %{"skip_binder" => parent}}},
           %{"Ident" => ["saturating_add", 0]}
         ], [scalar, scalar], scalar} ->
          if scalar == %{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}} and
               parent_type(parent, refs) == scalar and generic_shape?(generics, 0, 0) do
            %{
              rust_name: "core::num::{u64}::saturating_add",
              lean: "Aeneas.Std.core.num.U64.saturating_add",
              builtin: true,
              can_fail: false,
              lift: true,
              label:
                "Aeneas bounded u64 saturating addition model; Rust core implementation not verified"
            }
          end

        {[
           %{"Ident" => ["core", 0]},
           %{"Ident" => ["slice", 0]},
           %{"Impl" => %{"Ty" => %{"skip_binder" => parent}}},
           %{"Ident" => ["len", 0]}
         ],
         [
           %{
             "Ref" => [
               %{"Var" => %{"Free" => 0}},
               %{"Slice" => [%{"TypeVar" => %{"Free" => 0}}, nil]},
               "Shared"
             ]
           }
         ], %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}} ->
          if parent_type(parent, refs) == %{"Slice" => [%{"TypeVar" => %{"Free" => 0}}, nil]} and
               generic_shape?(generics, 1, 1) do
            %{
              rust_name: "core::slice::{[@T]}::len",
              lean: "Aeneas.Std.Slice.len",
              builtin: true,
              can_fail: false,
              lift: false,
              label:
                "Aeneas standard shared slice length model; Rust core implementation not verified"
            }
          end

        {[
           %{"Ident" => ["rustler", 0]},
           %{"Ident" => ["types", 0]},
           %{"Ident" => ["binary", 0]},
           %{"Impl" => %{"Ty" => %{"skip_binder" => parent}}},
           %{"Ident" => ["as_slice", 0]}
         ], [%{"Ref" => [%{"Var" => %{"Free" => 1}}, %{"Adt" => binary}, "Shared"]}],
         %{
           "Ref" => [
             %{"Var" => %{"Free" => 0}},
             %{"Slice" => [%{"Scalar" => %{"Integer" => %{"Unsigned" => "U8"}}}, nil]},
             "Shared"
           ]
         }} ->
          if :rustler_binary_as_slice in enabled and generic_shape?(generics, 2, 0) and
               parent_type(parent, refs) == %{"Adt" => binary} and
               binary_type?(binary, translated) do
            %{
              rust_name: "rustler::types::binary::{rustler::types::binary::Binary<'a>}::as_slice",
              lean: "Lynx.Rustler.binaryAsSlice",
              builtin: false,
              can_fail: true,
              lift: true,
              label:
                "Rustler 0.38/0.39 as_slice: immutable bytes and valid pointer assumed at the unverified FFI boundary; size bounded by isize::MAX"
            }
          end

        _ ->
          nil
      end
    end
  end

  defp match_function(_, _, _, _), do: nil

  defp candidate?(
         [
           %{"Ident" => ["core", 0]},
           %{"Ident" => ["num", 0]},
           %{"Impl" => _},
           %{"Ident" => [operation, 0]}
         ],
         _
       )
       when operation in ["saturating_add", "checked_add", "checked_mul"],
       do: true

  defp candidate?(
         [
           %{"Ident" => ["core", 0]},
           %{"Ident" => ["slice", 0]},
           %{"Impl" => _},
           %{"Ident" => ["len", 0]}
         ],
         _
       ),
       do: true

  defp candidate?(
         [
           %{"Ident" => ["rustler", 0]},
           %{"Ident" => ["types", 0]},
           %{"Ident" => ["binary", 0]},
           %{"Impl" => _},
           %{"Ident" => ["as_slice", 0]}
         ],
         enabled
       ),
       do: :rustler_binary_as_slice in enabled

  defp candidate?(
         [%{"Ident" => ["core", 0]}, %{"Ident" => ["mem", 0]}, %{"Ident" => ["replace", 0]}],
         _
       ),
       do: true

  defp candidate?(_, _), do: false

  defp generic_shape?(
         %{
           "regions" => region_parameters,
           "types" => type_parameters,
           "const_generics" => [],
           "trait_clauses" => [],
           "trait_type_constraints" => []
         },
         regions,
         types
       )
       when is_list(region_parameters) and is_list(type_parameters) do
    parameter_indices?(region_parameters, regions) and parameter_indices?(type_parameters, types)
  end

  defp generic_shape?(_, _, _), do: false

  defp parameter_indices?(parameters, count) do
    length(parameters) == count and
      Enum.all?(Enum.with_index(parameters), fn
        {%{"index" => index}, index} -> true
        _ -> false
      end)
  end

  defp binary_type?(
         %{
           "id" => id,
           "builtin" => nil,
           "generics" => %{
             "regions" => [%{"Var" => %{"Free" => 0}}],
             "types" => [],
             "const_generics" => [],
             "trait_refs" => []
           }
         },
         translated
       ) do
    Enum.any?(translated["type_decls"], fn
      %{
        "def_id" => ^id,
        "kind" => "Opaque",
        "item_meta" => %{
          "name" => [
            %{"Ident" => ["rustler", 0]},
            %{"Ident" => ["types", 0]},
            %{"Ident" => ["binary", 0]},
            %{"Ident" => ["Binary", 0]}
          ]
        }
      } ->
        true

      _ ->
        false
    end)
  end

  defp binary_type?(_, _), do: false

  # Instantiate free variables in a declaration's field type; bound variables
  # under nested binders retain their own identity.
  def instantiate(%{"TypeVar" => %{"Free" => index}}, args), do: Enum.fetch!(args["types"], index)
  def instantiate(%{"Var" => %{"Free" => index}}, args), do: Enum.fetch!(args["regions"], index)

  def instantiate(map, args) when is_map(map),
    do: Map.new(map, fn {key, value} -> {key, instantiate(value, args)} end)

  def instantiate(list, args) when is_list(list), do: Enum.map(list, &instantiate(&1, args))
  def instantiate(value, _), do: value

  def expand(%{"Value" => [_, value]}, refs), do: expand(value, refs)

  def expand(%{"Deduplicated" => id}, refs) do
    case Map.fetch(refs, id) do
      {:ok, type} -> expand(type, refs)
      :error -> %{"UnknownTypeReference" => id}
    end
  end

  def expand(value, refs) when is_map(value),
    do: Map.new(value, fn {key, value} -> {key, expand(value, refs)} end)

  def expand(values, refs) when is_list(values), do: Enum.map(values, &expand(&1, refs))
  def expand(value, _), do: value

  # The impl's parent type is under its own binder, while its method signature
  # uses free generic indices. Compare them in the same context.
  defp parent_type(type, refs), do: type |> expand(refs) |> free_parent()
  defp free_parent(%{"Bound" => [0, index]}), do: %{"Free" => index}

  defp free_parent(value) when is_map(value),
    do: Map.new(value, fn {key, value} -> {key, free_parent(value)} end)

  defp free_parent(value) when is_list(value), do: Enum.map(value, &free_parent/1)
  defp free_parent(value), do: value
end
